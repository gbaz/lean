/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"

namespace lean {
static name * g_equations_name  = nullptr;
static name * g_equation_name   = nullptr;
static name * g_decreasing_name = nullptr;

[[ noreturn ]] static void throw_eqs_ex() { throw exception("unexpected occurrence of 'equations' expression"); }
[[ noreturn ]] static void throw_eq_ex() { throw exception("unexpected occurrence of 'equation' expression"); }
[[ noreturn ]] static void throw_dec_ex() { throw exception("unexpected occurrence of 'decreasing' expression"); }

class equations_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_equations_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_eqs_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_eqs_ex(); }
    virtual void write(serializer &) const { throw_eqs_ex(); }
};

class equation_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const { return *g_equation_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const { throw_eq_ex(); }
    virtual optional<expr> expand(expr const &, extension_context &) const { throw_eq_ex(); }
    virtual void write(serializer &) const { throw_eq_ex(); }
};

class decreasing_macro_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception("invalid 'decreasing' expression, incorrect number of arguments");
    }
public:
    decreasing_macro_cell() {}
    virtual name get_name() const { return *g_decreasing_name; }
    virtual pair<expr, constraint_seq> get_type(expr const & m, extension_context & ctx) const {
        check_macro(m);
        return ctx.infer_type(macro_arg(m, 0));
    }
    virtual optional<expr> expand(expr const & m, extension_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer &) const { throw_dec_ex(); }
};

static macro_definition * g_equations  = nullptr;
static macro_definition * g_equation   = nullptr;
static macro_definition * g_decreasing = nullptr;

bool is_equation(expr const & e) { return is_macro(e) && macro_def(e) == *g_equation; }
expr const & equation_lhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 0); }
expr const & equation_rhs(expr const & e) { lean_assert(is_equation(e)); return macro_arg(e, 1); }
expr mk_equation(expr const & lhs, expr const & rhs) {
    expr args[2] = { lhs, rhs };
    return mk_macro(*g_equation, 2, args);
}

bool is_decreasing(expr const & e) { return is_macro(e) && macro_def(e) == *g_decreasing; }
expr const & decreasing_app(expr const & e) { lean_assert(is_decreasing(e)); return macro_arg(e, 0); }
expr const & decreasing_proof(expr const & e) { lean_assert(is_decreasing(e)); return macro_arg(e, 1); }
expr mk_decreasing(expr const & t, expr const & H) {
    expr args[2] = { t, H };
    return mk_macro(*g_decreasing, 2, args);
}

bool is_equations(expr const & e) { return is_macro(e) && macro_def(e) == *g_equations; }
bool is_wf_equations_core(expr const & e) {
    lean_assert(is_equations(e));
    return !is_equation(macro_arg(e, macro_num_args(e) - 1));
}
bool is_wf_equations(expr const & e) { return is_equations(e) && is_wf_equations_core(e); }
unsigned equations_size(expr const & e) {
    if (is_wf_equations_core(e))
        return macro_num_args(e) - 1;
    else
        return macro_num_args(e);
}
void to_equations(expr const & e, buffer<expr> & eqns) {
    lean_assert(is_equation(e));
    unsigned sz = equations_size(e);
    for (unsigned i = 0; i < sz; i++)
        eqns.push_back(macro_arg(e, i));
}
expr const & equations_wf_proof(expr const & e) {
    lean_assert(is_wf_equations(e));
    return macro_arg(e, macro_num_args(e) - 1);
}
expr mk_equations(unsigned num, expr const * eqns) {
    lean_assert(std::all_of(eqns, eqns+num, is_equation));
    lean_assert(num > 0);
    return mk_macro(*g_equations, num, eqns);
}
expr mk_equations(unsigned num, expr const * eqns, expr const & Hwf) {
    lean_assert(std::all_of(eqns, eqns+num, is_equation));
    lean_assert(num > 0);
    buffer<expr> args;
    args.append(num, eqns);
    args.push_back(Hwf);
    return mk_macro(*g_equations, args.size(), args.data());
}

void initialize_equations() {
    g_equations_name  = new name("equations");
    g_equation_name   = new name("equation");
    g_decreasing_name = new name("decreasing");
    g_equations       = new macro_definition(new equations_macro_cell());
    g_equation        = new macro_definition(new equation_macro_cell());
    g_decreasing      = new macro_definition(new decreasing_macro_cell());
}

void finalize_equations() {
    delete g_equations;
    delete g_equation;
    delete g_decreasing;
    delete g_equations_name;
    delete g_equation_name;
    delete g_decreasing_name;
}
}