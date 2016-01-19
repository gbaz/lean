/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <algorithm>
#include "library/trace.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/replace_visitor.h"
#include "library/blast/util.h"
#include "library/blast/trace.h"
#include "library/blast/blast.h"
#include "library/blast/state.h"

namespace lean {
namespace blast {
static name * g_prefix = nullptr;
static name * g_H      = nullptr;

bool metavar_decl::contains_href(expr const & h) const {
    return contains_href(href_index(h));
}

bool metavar_decl::restrict_context_using(metavar_decl const & other) {
    buffer<unsigned> to_erase;
    m_assumptions.for_each([&](unsigned hidx) {
            if (!other.contains_href(hidx))
                to_erase.push_back(hidx);
        });
    for (unsigned hidx : to_erase)
        m_assumptions.erase(hidx);
    return !to_erase.empty();
}

class extension_manager {
    std::vector<branch_extension *> m_exts;
public:
    ~extension_manager() {
        for (auto ext : m_exts)
            ext->dec_ref();
        m_exts.clear();
    }

    unsigned register_extension(branch_extension * ext) {
        ext->inc_ref();
        unsigned r = m_exts.size();
        m_exts.push_back(ext);
        return r;
    }

    bool has_ext(unsigned extid) const {
        return extid < m_exts.size();
    }

    branch_extension * get_initial(unsigned extid) {
        return m_exts[extid];
    }

    unsigned get_num_extensions() const {
        return m_exts.size();
    }
};

static extension_manager * g_extension_manager = nullptr;

static extension_manager & get_extension_manager() {
    return *g_extension_manager;
}

unsigned register_branch_extension(branch_extension * initial) {
    return get_extension_manager().register_extension(initial);
}

branch::branch() {
    unsigned n = get_extension_manager().get_num_extensions();
    m_extensions = new branch_extension*[n];
    for (unsigned i = 0; i < n; i++)
        m_extensions[i] = nullptr;
}

branch::~branch() {
    unsigned n = get_extension_manager().get_num_extensions();
    for (unsigned i = 0; i < n; i++) {
        if (m_extensions[i])
            m_extensions[i]->dec_ref();
    }
    delete m_extensions;
}

branch::branch(branch const & b):
    m_hyp_decls(b.m_hyp_decls),
    m_assumption(b.m_assumption),
    m_active(b.m_active),
    m_todo_queue(b.m_todo_queue),
    m_forward_deps(b.m_forward_deps),
    m_target(b.m_target),
    m_target_deps(b.m_target_deps),
    m_hyp_index(b.m_hyp_index) {
    unsigned n = get_extension_manager().get_num_extensions();
    m_extensions = new branch_extension*[n];
    for (unsigned i = 0; i < n; i++) {
        m_extensions[i] = b.m_extensions[i];
        if (m_extensions[i])
            m_extensions[i]->inc_ref();
    }
}

branch::branch(branch && b):
    m_hyp_decls(std::move(b.m_hyp_decls)),
    m_assumption(std::move(b.m_assumption)),
    m_active(std::move(b.m_active)),
    m_todo_queue(std::move(b.m_todo_queue)),
    m_forward_deps(std::move(b.m_forward_deps)),
    m_target(std::move(b.m_target)),
    m_target_deps(std::move(b.m_target_deps)),
    m_hyp_index(std::move(b.m_hyp_index)) {
    unsigned n = get_extension_manager().get_num_extensions();
    m_extensions = new branch_extension*[n];
    for (unsigned i = 0; i < n; i++) {
        m_extensions[i]   = b.m_extensions[i];
        b.m_extensions[i] = nullptr;
    }
}

void branch::swap(branch & b) {
    std::swap(m_hyp_decls, b.m_hyp_decls);
    std::swap(m_assumption, b.m_assumption);
    std::swap(m_active, b.m_active);
    std::swap(m_todo_queue, b.m_todo_queue);
    std::swap(m_hyp_index, b.m_hyp_index);
    std::swap(m_forward_deps, b.m_forward_deps);
    std::swap(m_target, b.m_target);
    std::swap(m_target_deps, b.m_target_deps);
    std::swap(m_extensions, b.m_extensions);
}

branch & branch::operator=(branch s) {
    swap(s);
    return *this;
}

state::state() {}

metavar_decl const * state::get_metavar_decl(expr const & e) const {
    return get_metavar_decl(mref_index(e));
}

expr state::mk_metavar(hypothesis_idx_set const & c, expr const & type) {
    unsigned midx = mk_mref_idx();
    m_metavar_decls.insert(midx, metavar_decl(c, type));
    return blast::mk_mref(midx);
}

expr state::mk_metavar(hypothesis_idx_buffer const & b, expr const & type) {
    hypothesis_idx_set ctx;
    for (unsigned const & hidx : b)
        ctx.insert(hidx);
    return mk_metavar(ctx, type);
}

expr state::mk_metavar(expr const & type) {
    return state::mk_metavar(get_assumptions(), type);
}

bool state::is_uref_assigned(level const & l) const {
    return m_uassignment.contains(uref_index(l));
}

/* u := l */
void state::assign_uref(level const & u, level const & l) {
    m_uassignment.insert(uref_index(u), l);
}

level const * state::get_uref_assignment(level const & l) const {
    return m_uassignment.find(uref_index(l));
}

bool state::is_mref_assigned(expr const & e) const {
    lean_assert(is_mref(e));
    return m_eassignment.contains(mref_index(e));
}

expr const * state::get_mref_assignment(expr const & e) const {
    return m_eassignment.find(mref_index(e));
}

void state::assign_mref(expr const & m, expr const & e) {
    m_eassignment.insert(mref_index(m), e);
}

void state::restrict_mref_context_using(expr const & mref1, expr const & mref2) {
    metavar_decl const * d1 = m_metavar_decls.find(mref_index(mref1));
    metavar_decl const * d2 = m_metavar_decls.find(mref_index(mref2));
    lean_assert(d1);
    lean_assert(d2);
    metavar_decl new_d1(*d1);
    if (new_d1.restrict_context_using(*d2))
        m_metavar_decls.insert(mref_index(mref1), new_d1);
}

hypothesis const & state::get_hypothesis_decl(expr const & h) const {
    return get_hypothesis_decl(href_index(h));
}

expr state::to_kernel_expr(expr const & e, hypothesis_idx_map<expr> & hidx2local, metavar_idx_map<expr> & midx2meta) const {
    return lean::replace(e, [&](expr const & e) {
            if (is_href(e)) {
                unsigned hidx = href_index(e);
                if (auto r = hidx2local.find(hidx)) {
                    return some_expr(*r);
                } else {
                    hypothesis const & h = get_hypothesis_decl(hidx);
                    // after we add support for let-decls in goals, we must convert back h->get_value() if it is available
                    expr new_h = lean::mk_local(name(name("H"), hidx),
                                                h.get_name(),
                                                to_kernel_expr(h.get_type(), hidx2local, midx2meta),
                                                binder_info());
                    hidx2local.insert(hidx, new_h);
                    return some_expr(new_h);
                }
            } else if (is_mref(e)) {
                unsigned midx = mref_index(e);
                if (auto r = midx2meta.find(midx)) {
                    return some_expr(*r);
                } else {
                    metavar_decl const * decl = m_metavar_decls.find(midx);
                    lean_assert(decl);
                    buffer<expr> ctx;
                    decl->get_assumptions().for_each([&](unsigned hidx) {
                            if (auto h = hidx2local.find(hidx))
                                ctx.push_back(*h);
                            else
                                ctx.push_back(to_kernel_expr(mk_href(hidx), hidx2local, midx2meta));
                        });
                    expr type     = to_kernel_expr(decl->get_type(), hidx2local, midx2meta);
                    expr new_type = Pi(ctx, type);
                    expr new_mvar = lean::mk_metavar(name(name("M"), mref_index(e)), new_type);
                    expr new_meta = mk_app(new_mvar, ctx);
                    midx2meta.insert(mref_index(e), new_meta);
                    return some_expr(new_meta);
                }
            } else {
                return none_expr();
            }
        });
}

expr state::to_kernel_expr(expr const & e) const {
    hypothesis_idx_map<expr> hidx2local;
    metavar_idx_map<expr>    midx2meta;
    return to_kernel_expr(e, hidx2local, midx2meta);
}

static name mk_name(name const & n, name_set & already_used) {
    name curr    = n;
    unsigned idx = 1;
    while (true) {
        if (!already_used.contains(curr)) {
            already_used.insert(curr);
            return curr;
        }
        curr = n.append_after(idx);
        idx++;
    }
}

goal state::to_goal(bool include_inactive) const {
    hypothesis_idx_map<expr> hidx2local;
    metavar_idx_map<expr>    midx2meta;
    hypothesis_idx_buffer hidxs;
    get_sorted_hypotheses(hidxs);
    buffer<expr> hyps;
    name_set already_used;
    for (unsigned hidx : hidxs) {
        if (!include_inactive && !is_active(hidx)) {
            break; // inactive hypotheses occur after active ones after sorting
        }
        hypothesis const & h = get_hypothesis_decl(hidx);
        // after we add support for let-decls in goals, we must convert back h->get_value() if it is available
        expr new_h = lean::mk_local(name(name("H"), hidx),
                                    mk_name(h.get_name(), already_used),
                                    to_kernel_expr(h.get_type(), hidx2local, midx2meta),
                                    binder_info());
        hidx2local.insert(hidx, new_h);
        hyps.push_back(new_h);
    }
    expr new_target    = to_kernel_expr(get_target(), hidx2local, midx2meta);
    expr new_mvar_type = Pi(hyps, new_target);
    expr new_mvar      = lean::mk_metavar(name("M"), new_mvar_type);
    expr new_meta      = mk_app(new_mvar, hyps);
    return goal(new_meta, new_target);
}

void state::display_active(std::ostream & out) const {
    out << "active := {";
    bool first = true;
    m_branch.m_active.for_each([&](hypothesis_idx hidx) {
            if (first) first = false; else out << ", ";
            out << get_hypothesis_decl(hidx).get_name();
        });
    out << "}\n";
}

void state::display(io_state_stream const & ios, bool include_inactive) const {
    ios << mk_pair(to_goal(include_inactive).pp(ios.get_formatter()), ios.get_options()) << "\n";
}

void state::display(environment const & env, io_state const & ios, bool include_inactive) const {
    formatter fmt = ios.get_formatter_factory()(env, ios.get_options());
    auto & out = ios.get_diagnostic_channel();
    out << mk_pair(to_goal(include_inactive).pp(fmt), ios.get_options()) << "\n";
}

bool state::has_assigned_uref(level const & l) const {
    if (!has_meta(l))
        return false;
    if (m_uassignment.empty())
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (is_uref(l) && is_uref_assigned(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

bool state::has_assigned_uref(levels const & ls) const {
    for (level const & l : ls) {
        if (has_assigned_uref(l))
            return true;
    }
    return false;
}

bool state::has_assigned_uref_mref(expr const & e) const {
    if (!has_mref(e) && !has_univ_metavar(e))
        return false;
    if (m_eassignment.empty() && m_uassignment.empty())
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_mref(e) && !has_univ_metavar(e))
                return false; // stop search
            if (found)
                return false; // stop search
            if ((is_mref(e) && is_mref_assigned(e)) ||
                (is_constant(e) && has_assigned_uref(const_levels(e))) ||
                (is_sort(e) && has_assigned_uref(sort_level(e)))) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

level state::instantiate_urefs(level const & l) {
    if (!has_assigned_uref(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_uref(l)) {
                level const * v1 = get_uref_assignment(l);
                if (v1) {
                    level v2 = instantiate_urefs(*v1);
                    if (*v1 != v2) {
                        assign_uref(l, v2);
                        return some_level(v2);
                    } else {
                        return some_level(*v1);
                    }
                }
            }
            return none_level();
        });
}

struct instantiate_urefs_mrefs_fn : public replace_visitor {
    state & m_state;

    level visit_level(level const & l) {
        return m_state.instantiate_urefs(l);
    }

    levels visit_levels(levels const & ls) {
        return map_reuse(ls,
                         [&](level const & l) { return visit_level(l); },
                         [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
    }

    virtual expr visit_sort(expr const & s) {
        return update_sort(s, visit_level(sort_level(s)));
    }

    virtual expr visit_constant(expr const & c) {
        return update_constant(c, visit_levels(const_levels(c)));
    }

    virtual expr visit_local(expr const & e) {
        if (is_href(e)) {
            return e;
        } else {
            return update_mlocal(e, visit(mlocal_type(e)));
        }
    }

    virtual expr visit_meta(expr const & m) {
        lean_assert(is_mref(m));
        if (auto v1 = m_state.get_mref_assignment(m)) {
            if (!has_mref(*v1)) {
                return *v1;
            } else {
                expr v2 = m_state.instantiate_urefs_mrefs(*v1);
                if (v2 != *v1)
                    m_state.assign_mref(m, v2);
                return v2;
            }
        } else {
            return m;
        }
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr const & f = get_app_rev_args(e, args);
        if (is_mref(f)) {
            if (auto v = m_state.get_mref_assignment(f)) {
                expr new_app = apply_beta(*v, args.size(), args.data());
                if (has_mref(new_app))
                    return visit(new_app);
                else
                    return new_app;
            }
        }
        expr new_f = visit(f);
        buffer<expr> new_args;
        bool modified = !is_eqp(new_f, f);
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            if (!is_eqp(arg, new_arg))
                modified = true;
            new_args.push_back(new_arg);
        }
        if (!modified)
            return e;
        else
            return mk_rev_app(new_f, new_args, e.get_tag());
    }

    virtual expr visit_macro(expr const & e) {
        lean_assert(is_macro(e));
        buffer<expr> new_args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            new_args.push_back(visit(macro_arg(e, i)));
        return update_macro(e, new_args.size(), new_args.data());
    }

    virtual expr visit(expr const & e) {
        if (!has_mref(e) && !has_univ_metavar(e))
            return e;
        else
            return replace_visitor::visit(e);
    }

public:
    instantiate_urefs_mrefs_fn(state & s):m_state(s) {}
    expr operator()(expr const & e) { return visit(e); }
};

expr state::instantiate_urefs_mrefs(expr const & e) {
    if (!has_assigned_uref_mref(e))
        return e;
    else
        return instantiate_urefs_mrefs_fn(*this)(e);
}

#ifdef LEAN_DEBUG
bool state::check_hypothesis(expr const & e, unsigned hidx, hypothesis const & h) const {
    lean_assert(closed(e));
    for_each(e, [&](expr const & n, unsigned) {
            if (is_href(n)) {
                lean_assert(h.depends_on(n));
                lean_assert(hidx_depends_on(hidx, href_index(n)));
            }
            return true;
        });
    return true;
}

bool state::check_hypothesis(unsigned hidx, hypothesis const & h) const {
    if (!h.is_dead()) {
        lean_assert(check_hypothesis(h.get_type(), hidx, h));
    }
    return true;
}

bool state::check_target() const {
    lean_assert(closed(get_target()));
    for_each(get_target(), [&](expr const & n, unsigned) {
            if (is_href(n)) {
                lean_assert(target_depends_on(n));
            }
            return true;
        });
    return true;
}

bool state::check_invariant() const {
    for_each_hypothesis([&](unsigned hidx, hypothesis const & h) {
            lean_assert(check_hypothesis(hidx, h));
        });
    lean_assert(check_target());
    return true;
}
#endif

struct hypothesis_dep_depth_lt {
    state const & m_state;

    hypothesis_dep_depth_lt(state const & s): m_state(s) {}
    bool operator()(unsigned hidx1, unsigned hidx2) const {
        hypothesis const & h1 = m_state.get_hypothesis_decl(hidx1);
        hypothesis const & h2 = m_state.get_hypothesis_decl(hidx2);
        bool act1             = true; // m_state.is_active(hidx1);
        bool act2             = true; // m_state.is_active(hidx2);
        if (act1 != act2) {
            return act1 && !act2; // active hypotheses should occur before non-active ones
        } else if (act1) {
            lean_assert(act1 && act2);
            if (h1.get_dep_depth() != h2.get_dep_depth())
                return h1.get_dep_depth() < h2.get_dep_depth();
            else
                return hidx1 < hidx2;
        } else {
            // for inactive hypotheses we just compare hidx's
            lean_assert(!act1 && !act2);
            return hidx1 < hidx2;
        }
    }
};

void state::get_sorted_hypotheses(hypothesis_idx_buffer & r) const {
    m_branch.m_hyp_decls.for_each([&](unsigned hidx, hypothesis const & h) {
            if (!h.is_dead())
                r.push_back(hidx);
        });
    sort_hypotheses(r);
}

void state::sort_hypotheses(hypothesis_idx_buffer & r) const {
    std::sort(r.begin(), r.end(), hypothesis_dep_depth_lt(*this));
}

void state::sort_hypotheses(hypothesis_idx_buffer_set & r) const {
    std::sort(r.m_buffer.begin(), r.m_buffer.end(), hypothesis_dep_depth_lt(*this));
}

void state::to_hrefs(hypothesis_idx_buffer const & hidxs, buffer<expr> & r) const {
    for (hypothesis_idx hidx : hidxs)
        r.push_back(get_hypothesis_decl(hidx).get_self());
}

void state::add_forward_dep(unsigned hidx_user, unsigned hidx_provider) {
    if (auto s = m_branch.m_forward_deps.find(hidx_provider)) {
        if (!s->contains(hidx_user)) {
            hypothesis_idx_set new_s(*s);
            new_s.insert(hidx_user);
            m_branch.m_forward_deps.insert(hidx_provider, new_s);
        }
    } else {
        hypothesis_idx_set new_s;
        new_s.insert(hidx_user);
        m_branch.m_forward_deps.insert(hidx_provider, new_s);
    }
}

void state::del_forward_dep(unsigned hidx_user, unsigned hidx_provider) {
    auto s = m_branch.m_forward_deps.find(hidx_provider);
    lean_assert(s);
    lean_assert(s->contains(hidx_user));
    hypothesis_idx_set new_s(*s);
    new_s.erase(hidx_user);
    m_branch.m_forward_deps.insert(hidx_provider, new_s);
}

void state::add_deps(expr const & e, hypothesis & h_user, unsigned hidx_user) {
    lean_assert(!h_user.is_dead());
    if (!has_href(e) && !has_mref(e))
        return; // nothing to be done
    for_each(e, [&](expr const & l, unsigned) {
            if (!has_href(l) && !has_mref(l)) {
                return false;
            } else if (is_href(l)) {
                unsigned hidx_provider = href_index(l);
                hypothesis const & h_provider = get_hypothesis_decl(hidx_provider);
                if (h_user.m_dep_depth <= h_provider.m_dep_depth)
                    h_user.m_dep_depth = h_provider.m_dep_depth + 1;
                if (!h_user.m_deps.contains(hidx_provider)) {
                    h_user.m_deps.insert(hidx_provider);
                    add_forward_dep(hidx_user, hidx_provider);
                }
                return false;
            } else {
                return true;
            }
        });
}

void state::add_deps(hypothesis & h_user, unsigned hidx_user) {
    add_deps(h_user.m_type, h_user, hidx_user);
}

double state::compute_weight(unsigned hidx, expr const & /* type */) {
    // TODO(Leo): use heuristics and machine learning for computing the weight of a new hypothesis
    // This method should not be here.
    return 1.0 / (static_cast<double>(hidx) + 1.0);
}

void state::add_todo_queue(hypothesis_idx hidx) {
    double w = compute_weight(hidx, get_hypothesis_decl(hidx).get_type());
    m_branch.m_todo_queue.insert(w, hidx);
}

expr state::mk_hypothesis(unsigned new_hidx, name const & n, expr const & type, optional<expr> const & value) {
    hypothesis new_h;
    expr r                = mk_href(new_hidx);
    new_h.m_name          = n;
    new_h.m_type          = type;
    new_h.m_value         = value;
    new_h.m_self          = r;
    new_h.m_proof_depth   = m_proof_depth;
    add_deps(new_h, new_hidx);
    m_branch.m_hyp_decls.insert(new_hidx, new_h);
    if (new_h.is_assumption())
        m_branch.m_assumption.insert(new_hidx);
    add_todo_queue(new_hidx);
    return r;
}

expr state::mk_hypothesis(name const & n, expr const & type, expr const & value) {
    return mk_hypothesis(mk_href_idx(), n, type, some_expr(value));
}

expr state::mk_hypothesis(expr const & type, expr const & value) {
    unsigned hidx = mk_href_idx();
    return mk_hypothesis(hidx, name(*g_H, hidx), type, some_expr(value));
}

expr state::mk_hypothesis(name const & n, expr const & type) {
    return mk_hypothesis(mk_href_idx(), n, type, none_expr());
}

expr state::mk_hypothesis(expr const & type) {
    unsigned hidx = mk_href_idx();
    return mk_hypothesis(hidx, name(*g_H, hidx), type, none_expr());
}

void state::del_hypotheses(buffer<hypothesis_idx> const & to_delete, hypothesis_idx_set const & to_delete_set) {
    for (hypothesis_idx h : to_delete) {
        hypothesis h_decl = get_hypothesis_decl(h);
        if (m_branch.m_active.contains(h)) {
            m_branch.m_active.erase(h);
            remove_from_indices(h_decl, h);
        }
        m_branch.m_assumption.erase(h);
        m_branch.m_forward_deps.erase(h);
        h_decl.m_deps.for_each([&](hypothesis_idx h_dep) {
                if (to_delete_set.contains(h_dep)) {
                    // we don't need to update forward deps for h_dep since
                    // it will also be deleted.
                    return;
                }
                del_forward_dep(h, h_dep);
            });
        h_decl.m_deps      = hypothesis_idx_set();
        h_decl.m_dead      = true;
        m_branch.m_hyp_decls.insert(h, h_decl);
        // Remark: we don't remove h from m_todo_queue. It is too expensive.
        // So, the method activate_hypothesis MUST check whether the candidate
        // hypothesis is dead or not.
    }
}

void state::collect_forward_deps(hypothesis_idx hidx, hypothesis_idx_buffer_set & result) {
    hypothesis_idx_buffer const & b = result.as_buffer();
    unsigned qhead = b.size();
    while (true) {
        hypothesis_idx_set s = get_direct_forward_deps(hidx);
        s.for_each([&](hypothesis_idx h_dep) { result.insert(h_dep); });
        if (qhead == b.size())
            return;
        hidx = b[qhead];
        qhead++;
    }
}

/* Return true iff the target type does not depend on any of the hypotheses in to_delete */
bool state::safe_to_delete(buffer<hypothesis_idx> const & to_delete) {
    for (hypothesis_idx h : to_delete) {
        if (m_branch.m_target_deps.contains(h)) {
            // h cannot be deleted since the target type
            // depends on it.
            return false;
        }
    }
    return true;
}

bool state::del_hypotheses(buffer<hypothesis_idx> const & hs) {
    hypothesis_idx_buffer_set to_delete;
    for (hypothesis_idx hidx : hs) {
        to_delete.insert(hidx);
        collect_forward_deps(hidx, to_delete);
    }
    if (!safe_to_delete(to_delete.as_buffer()))
        return false;
    del_hypotheses(to_delete.as_buffer(), to_delete.as_set());
    return true;
}

bool state::del_hypothesis(hypothesis_idx hidx) {
    hypothesis_idx_buffer_set to_delete;
    to_delete.insert(hidx);
    collect_forward_deps(hidx, to_delete);
    if (!safe_to_delete(to_delete.as_buffer()))
        return false;
    del_hypotheses(to_delete.as_buffer(), to_delete.as_set());
    return true;
}

hypothesis_idx_set state::get_direct_forward_deps(hypothesis_idx hidx) const {
    if (auto r = m_branch.m_forward_deps.find(hidx))
        return *r;
    else
        return hypothesis_idx_set();
}

optional<hypothesis_idx> state::contains_hypothesis(expr const & type) const {
    optional<hypothesis_idx> r;
    find_hypotheses(type, [&](hypothesis_idx hidx) {
            hypothesis const & h = get_hypothesis_decl(hidx);
            if (h.get_type() == type) {
                r = hidx;
                return false; // stop search
            } else {
                return true; // continue search
            }
        });
    return r;
}

branch_extension * state::get_extension_core(unsigned i) {
    branch_extension * ext = m_branch.m_extensions[i];
    if (ext && ext->get_rc() > 1) {
        branch_extension * new_ext = ext->clone();
        new_ext->inc_ref();
        ext->dec_ref();
        m_branch.m_extensions[i] = new_ext;
        return new_ext;
    }
    return ext;
}

branch_extension & state::get_extension(unsigned extid) {
    lean_assert(extid < get_extension_manager().get_num_extensions());
    if (!m_branch.m_extensions[extid]) {
        /* lazy initialization */
        branch_extension * ext = get_extension_manager().get_initial(extid)->clone();
        ext->inc_ref();
        m_branch.m_extensions[extid] = ext;
        lean_assert(ext->get_rc() == 1);
        ext->initialized();
        ext->target_updated();
        m_branch.m_active.for_each([&](hypothesis_idx hidx) {
                hypothesis const & h = get_hypothesis_decl(hidx);
                ext->hypothesis_activated(h, hidx);
            });
        return *ext;
    } else {
        branch_extension * ext = get_extension_core(extid);
        lean_assert(ext);
        return *ext;
    }
}

void state::deactivate_all() {
    m_branch.m_hyp_index = discr_tree();
    unsigned n = get_extension_manager().get_num_extensions();
    for (unsigned i = 0; i < n; i++) {
        if (m_branch.m_extensions[i]) {
            m_branch.m_extensions[i]->dec_ref();
            m_branch.m_extensions[i] = nullptr;
        }
    }
    m_branch.m_active.for_each([&](hypothesis_idx hidx) {
            add_todo_queue(hidx);
        });
    m_branch.m_active = hypothesis_idx_set();
}

static expr get_key_for(expr type) {
    while (is_not(type, type)) {}
    return type;
}

void state::update_indices(hypothesis_idx hidx) {
    hypothesis const & h = get_hypothesis_decl(hidx);
    unsigned n = get_extension_manager().get_num_extensions();
    for (unsigned i = 0; i < n; i++) {
        branch_extension * ext = get_extension_core(i);
        if (ext) ext->hypothesis_activated(h, hidx);
    }
    m_branch.m_hyp_index.insert(get_key_for(h.get_type()), h.get_self());
}

void state::remove_from_indices(hypothesis const & h, hypothesis_idx hidx) {
    unsigned n = get_extension_manager().get_num_extensions();
    for (unsigned i = 0; i < n; i++) {
        branch_extension * ext = get_extension_core(i);
        if (ext) ext->hypothesis_deleted(h, hidx);
    }
    m_branch.m_hyp_index.erase(get_key_for(h.get_type()), h.get_self());
}

void state::find_hypotheses(expr const & e, std::function<bool(hypothesis_idx)> const & fn) const { // NOLINT
    m_branch.m_hyp_index.find(get_key_for(e), [&](expr const & h) { return fn(href_index(h)); });
}

optional<unsigned> state::select_hypothesis_to_activate() {
    while (true) {
        if (m_branch.m_todo_queue.empty())
            return optional<unsigned>();
        unsigned hidx             = m_branch.m_todo_queue.erase_min();
        hypothesis const & h_decl = get_hypothesis_decl(hidx);
        if (!h_decl.is_dead()) {
            return optional<unsigned>(hidx);
        }
    }
}

void state::activate_hypothesis(hypothesis_idx hidx) {
    lean_trace_search(
        hypothesis const & h = get_hypothesis_decl(hidx);
        tout() << "activate " << h.get_name() << " : " << ppb(h.get_type()) << "\n";);
    lean_assert(!get_hypothesis_decl(hidx).is_dead());
    m_branch.m_active.insert(hidx);
    update_indices(hidx);
}

bool state::hidx_depends_on(unsigned hidx_user, unsigned hidx_provider) const {
    if (auto s = m_branch.m_forward_deps.find(hidx_provider)) {
        return s->contains(hidx_user);
    } else {
        return false;
    }
}

void state::set_target(expr const & t) {
    m_branch.m_target = t;
    m_branch.m_target_deps.clear();
    if (has_href(t) || has_mref(t)) {
        for_each(t, [&](expr const & e, unsigned) {
                if (!has_href(e) && !has_mref(e)) {
                    return false;
                } else if (is_href(e)) {
                    m_branch.m_target_deps.insert(href_index(e));
                    return false;
                } else {
                    return true;
                }
            });
    }
    unsigned n = get_extension_manager().get_num_extensions();
    for (unsigned i = 0; i < n; i++) {
        branch_extension * ext = get_extension_core(i);
        if (ext) ext->target_updated();
    }
}

bool state::target_depends_on(expr const & h) const {
    return target_depends_on(href_index(h));
}

struct expand_hrefs_fn : public replace_visitor {
    state const &      m_state;
    list<expr> const & m_hrefs;

    expand_hrefs_fn(state const & s, list<expr> const & hrefs):
        m_state(s), m_hrefs(hrefs) {}

    virtual expr visit_local(expr const & e) {
        if (is_href(e) && std::find(m_hrefs.begin(), m_hrefs.end(), e) != m_hrefs.end()) {
            hypothesis const & h = m_state.get_hypothesis_decl(e);
            if (h.get_value()) {
                return visit(*h.get_value());
            }
        }
        return replace_visitor::visit_local(e);
    }
};

expr state::expand_hrefs(expr const & e, list<expr> const & hrefs) const {
    return expand_hrefs_fn(*this, hrefs)(e);
}

auto state::save_assignment() -> assignment_snapshot {
    return assignment_snapshot(m_uassignment, m_metavar_decls, m_eassignment);
}

void state::restore_assignment(assignment_snapshot const & s) {
    std::tie(m_uassignment, m_metavar_decls, m_eassignment) = s;
}

expr state::mk_binding(bool is_lambda, unsigned num, expr const * hrefs, expr const & b) const {
    expr r     = abstract_locals(b, num, hrefs);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & h = hrefs[i];
        lean_assert(is_href(h));
        hypothesis const & hdecl = get_hypothesis_decl(h);
        expr t = abstract_locals(hdecl.get_type(), i, hrefs);
        if (is_lambda)
            r = ::lean::mk_lambda(hdecl.get_name(), t, r);
        else
            r = ::lean::mk_pi(hdecl.get_name(), t, r);
    }
    return r;
}

expr state::mk_lambda(list<expr> const & hrefs, expr const & b) const {
    buffer<expr> tmp;
    to_buffer(hrefs, tmp);
    return mk_lambda(tmp, b);
}

expr state::mk_pi(list<expr> const & hrefs, expr const & b) const {
    buffer<expr> tmp;
    to_buffer(hrefs, tmp);
    return mk_pi(tmp, b);
}

void initialize_state() {
    g_extension_manager = new extension_manager();
    g_prefix            = new name(name::mk_internal_unique_name());
    g_H                 = new name("H");
}

void finalize_state() {
    delete g_prefix;
    delete g_H;
    delete g_extension_manager;
}
}}
