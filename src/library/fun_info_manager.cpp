/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/replace_visitor.h"
#include "library/fun_info_manager.h"

namespace lean {
fun_info_manager::fun_info_manager(type_context & ctx):
    m_ctx(ctx) {
}

list<unsigned> fun_info_manager::collect_deps(expr const & type, buffer<expr> const & locals) {
    buffer<unsigned> deps;
    for_each(type, [&](expr const & e, unsigned) {
            if (m_ctx.is_tmp_local(e)) {
                unsigned idx;
                for (idx = 0; idx < locals.size(); idx++)
                    if (locals[idx] == e)
                        break;
                if (idx < locals.size() && std::find(deps.begin(), deps.end(), idx) == deps.end())
                    deps.push_back(idx);
            }
            return has_local(e); // continue the search only if e has locals
        });
    std::sort(deps.begin(), deps.end());
    return to_list(deps);
}

auto fun_info_manager::get(expr const & e) -> fun_info {
    if (auto r = m_fun_info.find(e))
        return *r;
    expr type = m_ctx.relaxed_try_to_pi(m_ctx.infer(e));
    buffer<param_info> info;
    buffer<expr> locals;
    while (is_pi(type)) {
        expr local      = m_ctx.mk_tmp_local_from_binding(type);
        expr local_type = m_ctx.infer(local);
        expr new_type   = m_ctx.relaxed_try_to_pi(instantiate(binding_body(type), local));
        bool is_prop    = m_ctx.is_prop(local_type);
        bool is_sub     = is_prop;
        bool is_dep     = !closed(binding_body(type));
        if (!is_sub) {
            // TODO(Leo): check if the following line is a performance bottleneck.
            is_sub = static_cast<bool>(m_ctx.mk_subsingleton_instance(local_type));
        }
        info.emplace_back(binding_info(type).is_implicit(),
                          binding_info(type).is_inst_implicit(),
                          is_prop, is_sub, is_dep, collect_deps(local_type, locals));
        locals.push_back(local);
        type = new_type;
    }
    fun_info r(info.size(), to_list(info), collect_deps(type, locals));
    m_fun_info.insert(e, r);
    return r;
}

auto fun_info_manager::get(expr const & e, unsigned nargs) -> fun_info {
    auto r = get(e);
    lean_assert(nargs <= r.get_arity());
    if (nargs == r.get_arity()) {
        return r;
    } else {
        buffer<param_info> pinfos;
        to_buffer(r.get_params_info(), pinfos);
        buffer<unsigned> rdeps;
        to_buffer(r.get_dependencies(), rdeps);
        for (unsigned i = nargs; i < pinfos.size(); i++) {
            for (auto d : pinfos[i].get_dependencies()) {
                if (std::find(rdeps.begin(), rdeps.end(), d) == rdeps.end())
                    rdeps.push_back(d);
            }
        }
        pinfos.shrink(nargs);
        return fun_info(nargs, to_list(pinfos), to_list(rdeps));
    }
}

struct replace_fn : public replace_visitor {
    fun_info_manager & m_infom;
    type_context &     m_ctx;
    unsigned           m_num;
    expr const *       m_from;
    expr const *       m_to;

    struct failed {};

    replace_fn(fun_info_manager & infom, unsigned n, expr const * ts, expr const * rs):
        m_infom(infom), m_ctx(infom.ctx()), m_num(n), m_from(ts), m_to(rs) {}

    virtual expr visit(expr const & e) {
        for (unsigned i = 0; i < m_num; i++) {
            if (e == m_from[i])
                return m_to[i];
        }
        return replace_visitor::visit(e);
    }

    virtual expr visit_mlocal(expr const & e) {
        return e;
    }

    virtual expr visit_binding(expr const & b) {
        expr new_domain = visit(binding_domain(b));
        expr l          = m_ctx.mk_tmp_local(binding_name(b), new_domain, binding_info(b));
        expr new_body   = abstract(visit(instantiate(binding_body(b), l)), l);
        return update_binding(b, new_domain, new_body);
    }

    virtual expr visit_app(expr const & e) {
        buffer<expr> args;
        expr f        = get_app_args(e, args);
        expr new_f    = visit(f);
        fun_info info = m_infom.get(f);
        if (info.get_arity() < args.size())
            throw failed();
        auto ps_info  = info.get_params_info();
        bool modified = f != new_f;
        buffer<expr> new_args;
        buffer<bool> to_check;
        bool has_to_check = false;
        for (expr const & arg : args) {
            expr new_arg = visit(arg);
            auto pinfo   = head(ps_info);
            bool c       = false;
            if (modified) {
                // if not argument has been modified, then there is nothing to be checked
                for (unsigned idx : pinfo.get_dependencies()) {
                    lean_assert(idx < new_args.size());
                    if (args[idx] != new_args[idx]) {
                        c = true;
                        has_to_check = true;
                        break;
                    }
                }
            }
            if (new_arg != arg) {
                modified = true;
            }
            to_check.push_back(c);
            new_args.push_back(new_arg);
            ps_info      = tail(ps_info);
        }
        lean_assert(args.size() == new_args.size());
        if (!modified)
            return e;
        expr new_e = mk_app(new_f, new_args);
        if (has_to_check) {
            lean_assert(to_check.size() == new_args.size());
            expr it    = new_e;
            unsigned i = to_check.size();
            while (i > 0) {
                --i;
                expr const & fn = app_fn(it);
                if (to_check[i]) {
                    expr fn_type  = m_ctx.whnf(m_ctx.infer(fn));
                    if (!is_pi(fn_type))
                        throw failed();
                    expr arg_type = m_ctx.infer(app_arg(it));
                    if (!m_ctx.is_def_eq(binding_domain(fn_type), arg_type))
                        throw failed();
                }
                it = fn;
            }
        }
        return new_e;
    }
};

optional<expr> replace(fun_info_manager & infom, expr const & e, unsigned n, expr const * ts, expr const * rs) {
    try {
        return some_expr(replace_fn(infom, n, ts, rs)(e));
    } catch (replace_fn::failed &) {
        return none_expr();
    }
}
}
