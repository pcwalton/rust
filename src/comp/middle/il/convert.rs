/* Converts checked ASTs to IL. */

import middle::il::il;
import middle::ty;
import syntax::ast;
import syntax::ast::node_id;
import std::vec;

fn convert_block(_tcx: ty::ctxt, _blk: ast::blk) -> @il::blk {
    // TODO
    ret @{
        n_temps: 0u,
        locals: @[],
        insts: @[]
    };
}

fn convert_fn(tcx: ty::ctxt, fun: ast::_fn, _tps: [ast::ty_param],
              id: node_id) -> @il::fun {
    ret @{
        tpt: ty::lookup_item_type(tcx, { crate: ast::local_crate, node: id }),
        proto: fun.proto,
        body: convert_block(tcx, fun.body)
    };
}

fn convert_item(tcx: ty::ctxt, ast_item: @ast::item) -> @il::item {
    let item = alt (ast_item.node) {
        ast::item_const(_, _) { fail }
        ast::item_fn(fun, tps) {
            il::item_fn(convert_fn(tcx, fun, tps, ast_item.id))
        }
        ast::item_mod(module) { il::item_mod(convert_mod(tcx, module)) }
        ast::item_native_mod(_) { fail }
        ast::item_ty(_, _) { fail }
        ast::item_tag(_, _) { fail }
    };
    ret @{ ident: ast_item.ident, item: item };
}

fn convert_mod(tcx: ty::ctxt, module: ast::_mod) -> @il::module {
    ret @{
        view_items: (),     // TODO
        items: @vec::map(bind convert_item(tcx, _), module.items)
    };
}

fn convert_crate(tcx: ty::ctxt, crate: @ast::crate) -> @il::crate {
    ret @{
        deps: (),
        attrs: @[],     // TODO
        module: convert_mod(tcx, crate.node.module)
    }
}

