// A pass that generates a call graph, useful for monomorphizing, debugging,
// and incremental recompilation.

import driver::session;
import middle::ty;
import syntax::ast;
import syntax::codemap::span;
import syntax::visit;
import std::ioivec;
import std::option;
import std::option::none;
import std::option::some;
import std::str;

type src = { node: ast::def_id, path: ast::ident[] };

type sig = { node: ast::def_id, types: ty::t[] };

type ref = {
    path_id: ast::node_id,  // The ID of the path node in the AST.
    sig: sig                // The signature of the item being referenced.
};

type entry = { from: src, to: @mutable (ref[]) };

type t = @mutable (entry[]);


// Call graph generation

type ctxt = {
    tcx: ty::ctxt,
    entries: t,
    cur_dests: option::t[@mutable (ref[])],
    path: ast::ident[]
};

fn visit_expr(e: &@ast::expr, cx: &ctxt, visitor: &visit::vt[ctxt]) {
    alt e.node {
        ast::expr_path(_) {
            alt cx.tcx.def_map.get(e.id) {
                ast::def_fn(dest_id, _) | ast::def_obj_field(dest_id) |
                ast::def_variant(dest_id, _) {
                    *option::get(cx.cur_dests) += ~[{
                        path_id: e.id,
                        sig: {
                            node: dest_id,
                            types: ty::expr_ty_params_and_ty(cx.tcx, e).params
                        }
                    }];
                }
                _ { /* no-op */ }
            }
        }
        _ { visit::visit_expr(e, cx, visitor); }
    }
}

fn visit_fn(f: &ast::_fn, tps: &ast::ty_param[], sp: &span, i: &ast::fn_ident,
            id: ast::node_id, cx: &ctxt, visitor: &visit::vt[ctxt]) {
    let dests = @mutable ~[];

    let new_path = cx.path;
    alt i {
        none. { /* no-op */ }
        some(name) { new_path += ~[name]; }
    }

    let subcx = { cur_dests: some(dests), path: new_path with cx };

    visit::visit_fn(f, tps, sp, i, id, subcx, visitor);

    *cx.entries += ~[{
        from: {
            node: { crate: ast::local_crate, node: id },
            path: subcx.path
        },
        to: dests
    }];
}

fn visit_item(i: &@ast::item, cx: &ctxt, visitor: &visit::vt[ctxt]) {
    let subcx = { path: cx.path + ~[i.ident] with cx };
    visit::visit_item(i, subcx, visitor);
}

// TODO: Don't build up the path unless we're pretty-printing.

fn create_call_graph(sess: &session::session, tcx: &ty::ctxt,
                     crate: &@ast::crate) -> t {
    let cx = {
        tcx: tcx,
        entries: @mutable ~[],
        cur_dests: none,
        path: ~[]
    };
    let visitor = visit::mk_vt(@{visit_fn: visit_fn,
                                 visit_expr: visit_expr
                                 with *visit::default_visitor()});
    visit::visit_crate(*crate, cx, visitor);

    let graph = cx.entries;
    if sess.get_opts().print_call_graph {
        pretty_print_call_graph(tcx, graph, ioivec::stdout());
    }

    ret graph;
}


// Call graph pretty-printing in dot format

fn pretty_print_call_graph(tcx: &ty::ctxt, cx: &t, writer: &ioivec::writer) {
    writer.write_line("digraph G {");

    for e in *cx {
        let entry = e;  // satisfy alias checker

        let s = #fmt("\"%d:%d\" [label=\"%s\"];",
                     entry.from.node.crate, entry.from.node.node,
                     str::connect_ivec(entry.from.path, "::"));
        writer.write_line(s);

        for r in *entry.to {
            let ref = r;   // satisfy alias checker

            let s = #fmt("\"%d:%d\" -> \"%d:%d\";",
                         entry.from.node.crate, entry.from.node.node,
                         ref.sig.node.crate, ref.sig.node.node);
            writer.write_line(s);
        }
    }

    writer.write_line("}");
}

