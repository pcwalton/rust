// Routines related to memory management.

import lib::llvm::llvm::ModuleRef;
import lib::llvm::llvm::ValueRef;
import middle::trans;
import middle::trans_common::bcx_ccx;
import middle::trans_common::bcx_tcx;
import middle::trans_common::block_ctxt;
import middle::trans_common::T_fn;
import middle::trans_common::T_i8;
import middle::trans_common::T_ptr;
import middle::trans_common::T_void;
import middle::ty;
import std::map::hashmap;
import std::option::none;

mod gc {

// Whether a box type is garbage-collected.
//
// TODO: It's not certain what the requirements are here.
fn box_type_requires_gc(cx : &ty::ctxt, ty : &ty::t) -> bool {
    ret true;
}

// Whether a type must be scanned by the garbage collector.
fn type_is_gc_relevant(cx : &ty::ctxt, ty : &ty::t) -> bool {
    alt ty::struct(cx, ty) {
        ty::ty_nil. | ty::ty_bot. | ty::ty_bool. | ty::ty_int. |
        ty::ty_float. | ty::ty_uint. | ty::ty_machine(_) | ty::ty_char. |
        ty::ty_str. | ty::ty_istr. | ty::ty_type. | ty::ty_native(_) |
        ty::ty_ptr(_) | ty::ty_port(_) | ty::ty_chan(_) | ty::ty_task. {
            ret false;
        }

        // Opaque types.
        ty::ty_fn(_,_,_,_,_) | ty::ty_native_fn(_,_,_) | ty::ty_obj(_) |
        ty::ty_param(_,_) {
            ret true;
        }

        // Boxed types.
        ty::ty_box(tm) { ret box_type_requires_gc(cx, tm.ty); }
        ty::ty_vec(tm) { ret box_type_requires_gc(cx, tm.ty); }

        // Structural types.
        ty::ty_tag(did, tps) {
            for variant in ty::tag_variants(cx, did) {
                // FIXME: Don't use mk_imm_tup here; it is slow.
                let tup_ty = ty::mk_imm_tup(cx, variant.args);
                tup_ty = ty::substitute_type_params(cx, tps, tup_ty);
                if type_is_gc_relevant(cx, tup_ty) { ret true; }
            }
            ret false;
        }
        ty::ty_ivec(tm) { ret type_is_gc_relevant(cx, tm.ty); }
        ty::ty_rec(flds) {
            for f in flds {
                if type_is_gc_relevant(cx, f.mt.ty) { ret true; }
            }
            ret false;
        }
        ty::ty_res(_, inner, tps) {
            let inner_sub = ty::substitute_type_params(cx, tps, inner);
            ret type_is_gc_relevant(cx, inner_sub);
        }
        ty::ty_constr(subtype, _) { ret type_is_gc_relevant(cx, subtype); }

        ty::ty_var(_) { fail "ty_var in type_is_gc_relevant"; }
    }
}

// Roots a garbage-collected value if it's GC-relevant by type analysis.
// |llslot| is an LLVM pointer representing the value.
fn root_if_necessary(cx : &@block_ctxt, llslot : ValueRef, typ : &ty::t)
        -> @block_ctxt {
    let bcx = cx;
    if !type_is_gc_relevant(bcx_tcx(bcx), typ) { ret; }

    let llgcroot = bcx_ccx(bcx).intrinsics.get("llvm.gcroot");
    llslot = bcx.build.PointerCast(llslot, T_ptr(T_ptr(T_i8())));

    let ti = none;
    let r = trans::get_tydesc(bcx, typ, true, ti);
    let lltydesc = r.val; bcx = r.bcx;

    lltydesc = bcx.build.PointerCast(lltydesc, T_ptr(T_i8()));
    bcx.build.Call(llgcroot, ~[llslot, lltydesc]);
    ret bcx;
}

fn insert_gc_intrinsics(llmod : ModuleRef,
                        intrinsics : &hashmap[str,ValueRef]) {
    let llgcroot = trans::decl_cdecl_fn(llmod, "llvm.gcroot",
                                        T_fn(~[T_ptr(T_ptr(T_i8())),
                                               T_ptr(T_i8())],
                                             T_void()));
    let llgcwrite = trans::decl_cdecl_fn(llmod, "llvm.gcwrite",
                                         T_fn(~[T_ptr(T_i8()), T_ptr(T_i8()),
                                                T_ptr(T_ptr(T_i8()))],
                                              T_void()));
    intrinsics.insert("llvm.gcroot", llgcroot);
    intrinsics.insert("llvm.gcwrite", llgcwrite);
}

} // end module gc

