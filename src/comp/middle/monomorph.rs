// Routines related to monomorphization, a new, experimental implementation
// strategy for generics.

import lib::llvm::llvm::ValueRef;
import middle::ast_map;
import middle::callgraph;
import middle::callgraph::ref;
import middle::callgraph::sig;
import middle::shape;
import middle::trans;
import middle::ty;
import syntax::ast;
import util::common;

import std::ivec;
import std::map;
import std::map::hashmap;
import std::str;

import lll = lib::llvm::llvm;
import tc = middle::trans_common;

// The information needed to instantiate a generic function.
type instn_info = {
    template: ValueRef,     // The generic template function.
    special: ValueRef,      // The specialized function.
    uses: ref[]             // The uses of generics in the function.
};

// A mapping from signatures to the info needed to instantiate the generic
// function.
type instns = hashmap[sig, instn_info];

type ctxt = {
    tcx: ty::ctxt,                              // The type context.
    instns: instns,                             // The type instantiations.
    item_ids: hashmap[ast::node_id,ValueRef],
    ast_map: ast_map::map
};


// Signature boilerplate

fn hash_sig(sig: &sig) -> uint {
    let h = 5381u;
    h *= 33u; h += sig.node.crate as uint;
    h *= 33u; h += sig.node.node as uint;
    for t in sig.types { h *= 33u; h += t as uint; }
    ret h;
}

fn eq_sig(a: &sig, b: &sig) -> bool {
    if a.node.crate != b.node.crate || a.node.node != b.node.node ||
           ivec::len(a.types) != ivec::len(b.types) {
        ret false;
    }
    let i = 0u;
    while i < ivec::len(a.types) {
        if a.types.(i) != b.types.(i) { ret false; }
        i += 1u;
    }
    ret true;
}


// Creates a context.
fn mk_ctxt(tcx: &ty::ctxt, item_ids: &hashmap[ast::node_id,ValueRef],
           ast_map: &ast_map::map) -> ctxt {
    ret {
        tcx: tcx,
        instns: map::mk_hashmap[sig,instn_info](hash_sig, eq_sig),
        item_ids: item_ids,
        ast_map: ast_map
    };
}

fn item_is_generic(cx: &ctxt, item_id: &ast::def_id) -> bool {
    // TODO: externals
    alt cx.ast_map.get(item_id.node) {
        ast_map::node_item(item) {
            alt item.node {
                ast::item_const(_,_) | ast::item_mod(_) |
                ast::item_native_mod(_) { ret false; }
                ast::item_fn(_, tps) { ret ivec::len(tps) > 0u; }
                ast::item_ty(_, tps) { ret ivec::len(tps) > 0u; }
                ast::item_tag(_, tps) { ret ivec::len(tps) > 0u; }
                ast::item_obj(_, tps, _) { ret ivec::len(tps) > 0u; }
                ast::item_res(_, _, tps, _) { ret ivec::len(tps) > 0u; }
            }
        }
        _ { fail "non-item in item_is_generic"; }
    }
}

// Uses the call graph to determine which specializations we need to generate.
// The provided |callback| generates the |ValueRef| declaration for each
// instantiation.
fn populate_instns(cx: &ctxt, callgraph: &callgraph::t,
                   callback: fn(&sig)->ValueRef) {
    let graph_map = common::new_def_hash[@mutable (ref[])]();
    let worklist: sig[] = ~[];
    for e in *callgraph {
        let entry = e;  // Satisfy alias checker.
        graph_map.insert(entry.from.node, entry.to);
        if !item_is_generic(cx, entry.from.node) {
            // Seed the worklist with this node.
            worklist += ~[{ node: entry.from.node, types: ~[] }];
        }
    }

    let i = 0u;
    while i < ivec::len(worklist) {
        let sig = worklist.(i);
        if !cx.instns.contains_key(sig) {   // TODO: Invert, use continue.
            // Add any references of generic items that this item references
            // to the worklist.
            let generic_refs = ~[];
            let refs = graph_map.get(sig.node);
            for r in *refs {
                let ref = r;    // Satisfy alias checker.
                if item_is_generic(cx, ref.sig.node) {
                    // This is a reference to a generic item that we need to
                    // monomorphize. First, substitute type parameters.
                    let new_types = ~[];
                    for typ in ref.sig.types {
                        new_types +=
                            ~[ty::substitute_type_params(cx.tcx, sig.types,
                                                         typ)];
                    }

                    // Now add the item to the worklist.
                    worklist += ~[{ node: ref.sig.node, types: new_types }];

                    generic_refs += ~[{
                        path_id: ref.path_id,
                        sig: { node: ref.sig.node, types: ref.sig.types }
                    }];
                }
            }

            // Now monomorphize the item.
            if item_is_generic(cx, sig.node) {
                cx.instns.insert(sig, {
                    template: cx.item_ids.get(sig.node.node), // TODO: externs
                    special: callback(sig),
                    uses: generic_refs
                });
            }
        }

        i += 1u;
    }
}


// Converts a polymorphic value declaration to a monomorphic value
// declaration.
fn transform_decl(ccx: &@tc::crate_ctxt, llval: ValueRef, sig: &sig) ->
        ValueRef {
    let llsubsttypes = ~[];
    for typ in sig.types {
        llsubsttypes += ~[trans::type_of(ccx, shape::fake_span(), typ)];
    }

    // TODO: Better names.
    let llpolyty = lll::LLVMGetElementType(tc::val_ty(llval));
    log_err tc::ty_str(ccx.tn, llpolyty);
    let llmonoty = lll::LLVMRustReplaceTypes(llpolyty,
                                             ivec::to_ptr(llsubsttypes),
                                             ivec::len(llsubsttypes));
    ret lll::LLVMAddFunction(ccx.llmod, str::buf("instantiated"), llmonoty);
}

