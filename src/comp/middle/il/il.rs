/* An intermediate language in three-address code. Can be straightforwardly
 * serialized or deserialized and monomorphized. */

import syntax::ast;
import std::option;

type tmp = uint;
type local = uint;
type ty = uint;

type lit = ast::lit_;
type ty_param = ast::kind;

type call = {
    fun: val,
    args: @[val],
    tail: bool
};

type arm = ();          /* TODO */

tag val {
    val_tmp(tmp);       /* a temporary */
    val_arg(uint);      /* a function argument */
    val_local(uint);    /* a local */
    val_global(uint);   /* a global */
}

// Instructions.
tag inst {
    inst_vec(ast::mutability, @[val]);
    inst_rec(ty, @[val], option::t<val>);
    inst_call(call);
    inst_tup([val]);
    inst_bind(val, option::t<val>);
    inst_binary(ast::binop, val, val);
    inst_unary(ast::unop, val);
    inst_lit(@lit);
    inst_cast(val, ty);
    inst_if(val, @blk, @blk);
    inst_while(val, @blk);
    inst_for(local, val, @blk);
    inst_do_while(val, @blk);
    inst_alt(val, @[arm]);
    inst_fn(fun);
    inst_blk(@blk);
    inst_move(val, val);
    inst_assign(val, val);
    inst_swap(val, val);
    inst_assign_op(ast::binop, val, val);
    inst_field(val, uint);
    inst_index(val, val);
    inst_fail(option::t<val>);
    inst_break;
    inst_cont;
    inst_ret(option::t<val>);
    inst_be(call);
    inst_log(int, val);
    inst_assert(val);
    inst_check(call);
}

type blk = {
    n_temps: uint,      /* The number of temporaries. */
    locals: @[ty],      /* The locals in the function. */
    insts: @[inst]
};

type fun = {
    tpt: ty::ty_param_kinds_and_ty,
    proto: ast::proto,
    body: @blk
};

type variant = ();  /* TODO */

/* Items. */
tag item_ {
    item_const(ty, @lit);
    item_fn(@fun);
    item_mod(@module);
    item_native_mod(@native_mod);
    item_ty(ty, @[ty_param]);
    item_tag(@[variant], @[ty_param]);
}

type item = {
    ident: str,
    item: item_
};

type module = {
    view_items: (),     // TODO
    items: @[@item]
};

type deps = ();         /* TODO */
type attr = ();         /* TODO */
type native_mod = ();   /* TODO */

type crate = {
    deps: deps,
    attrs: @[attr],
    module: @module
};

