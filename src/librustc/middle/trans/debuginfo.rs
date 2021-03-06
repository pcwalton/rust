// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
# Debug Info Module

This module serves the purpose of generating debug symbols. We use LLVM's
[source level debugging](http://llvm.org/docs/SourceLevelDebugging.html) features for generating
the debug information. The general principle is this:

Given the right metadata in the LLVM IR, the LLVM code generator is able to create DWARF debug
symbols for the given code. The [metadata](http://llvm.org/docs/LangRef.html#metadata-type) is
structured much like DWARF *debugging information entries* (DIE), representing type information
such as datatype layout, function signatures, block layout, variable location and scope information,
etc. It is the purpose of this module to generate correct metadata and insert it into the LLVM IR.

As the exact format of metadata trees may change between different LLVM versions, we now use LLVM
[DIBuilder](http://llvm.org/docs/doxygen/html/classllvm_1_1DIBuilder.html) to create metadata
where possible. This will hopefully ease the adaption of this module to future LLVM versions.

The public API of the module is a set of functions that will insert the correct metadata into the
LLVM IR when called with the right parameters. The module is thus driven from an outside client with
functions like `debuginfo::create_local_var_metadata(bcx: block, local: &ast::local)`.

Internally the module will try to reuse already created metadata by utilizing a cache. The way to
get a shared metadata node when needed is thus to just call the corresponding function in this
module:

    let file_metadata = file_metadata(crate_context, path);

The function will take care of probing the cache for an existing node for that exact file path.

All private state used by the module is stored within either the CrateDebugContext struct (owned by
the CrateContext) or the FunctionDebugContext (owned by the FunctionContext).

This file consists of three conceptual sections:
1. The public interface of the module
2. Module-internal metadata creation functions
3. Minor utility functions

*/


use driver::session;
use lib::llvm::llvm;
use lib::llvm::{ModuleRef, ContextRef, ValueRef};
use lib::llvm::debuginfo::*;
use middle::trans::common::*;
use middle::trans::machine;
use middle::trans::type_of;
use middle::trans::type_::Type;
use middle::trans::adt;
use middle::trans;
use middle::ty;
use middle::pat_util;
use util::ppaux::ty_to_str;

use std::c_str::ToCStr;
use std::hashmap::HashMap;
use std::libc::{c_uint, c_ulonglong, c_longlong};
use std::ptr;
use std::vec;
use syntax::codemap::Span;
use syntax::{ast, codemap, ast_util, ast_map, opt_vec};
use syntax::parse::token;
use syntax::parse::token::special_idents;

static DW_LANG_RUST: c_uint = 0x9000;

static DW_TAG_auto_variable: c_uint = 0x100;
static DW_TAG_arg_variable: c_uint = 0x101;

static DW_ATE_boolean: c_uint = 0x02;
static DW_ATE_float: c_uint = 0x04;
static DW_ATE_signed: c_uint = 0x05;
static DW_ATE_signed_char: c_uint = 0x06;
static DW_ATE_unsigned: c_uint = 0x07;
static DW_ATE_unsigned_char: c_uint = 0x08;




//=-------------------------------------------------------------------------------------------------
//  Public Interface of debuginfo module
//=-------------------------------------------------------------------------------------------------

/// A context object for maintaining all state needed by the debuginfo module.
pub struct CrateDebugContext {
    priv crate_file: ~str,
    priv llcontext: ContextRef,
    priv builder: DIBuilderRef,
    priv curr_loc: DebugLocation,
    priv created_files: HashMap<~str, DIFile>,
    priv created_types: HashMap<uint, DIType>,
}

impl CrateDebugContext {
    pub fn new(llmod: ModuleRef, crate: ~str) -> CrateDebugContext {
        debug!("CrateDebugContext::new");
        let builder = unsafe { llvm::LLVMDIBuilderCreate(llmod) };
        // DIBuilder inherits context from the module, so we'd better use the same one
        let llcontext = unsafe { llvm::LLVMGetModuleContext(llmod) };
        return CrateDebugContext {
            crate_file: crate,
            llcontext: llcontext,
            builder: builder,
            curr_loc: UnknownLocation,
            created_files: HashMap::new(),
            created_types: HashMap::new(),
        };
    }
}

pub enum FunctionDebugContext {
    priv FunctionDebugContext(~FunctionDebugContextData),
    priv DebugInfoDisabled,
    priv FunctionWithoutDebugInfo,
}

impl FunctionDebugContext {
    fn get_ref<'a>(&'a self, cx: &CrateContext, span: Span) -> &'a FunctionDebugContextData {
        match *self {
            FunctionDebugContext(~ref data) => data,
            DebugInfoDisabled => {
                cx.sess.span_bug(span, "debuginfo: Error trying to access FunctionDebugContext \
                                        although debug info is disabled!");
            }
            FunctionWithoutDebugInfo => {
                cx.sess.span_bug(span, "debuginfo: Error trying to access FunctionDebugContext \
                                        for function that should be ignored by debug info!");
            }
        }
    }

    fn get_mut_ref<'a>(&'a mut self,
                       cx: &CrateContext,
                       span: Span)
                    -> &'a mut FunctionDebugContextData {
        match *self {
            FunctionDebugContext(~ref mut data) => data,
            DebugInfoDisabled => {
                cx.sess.span_bug(span, "debuginfo: Error trying to access FunctionDebugContext \
                                        although debug info is disabled!");
            }
            FunctionWithoutDebugInfo => {
                cx.sess.span_bug(span, "debuginfo: Error trying to access FunctionDebugContext \
                                        for function that should be ignored by debug info!");
            }
        }
    }
}

struct FunctionDebugContextData {
    scope_map: HashMap<ast::NodeId, DIScope>,
    fn_metadata: DISubprogram,
    argument_counter: uint,
    source_locations_enabled: bool,
}

enum VariableAccess<'self> {
    // The llptr given is an alloca containing the variable's value
    DirectVariable { alloca: ValueRef },
    // The llptr given is an alloca containing the start of some pointer chain leading to the
    // variable's content.
    IndirectVariable { alloca: ValueRef, address_operations: &'self [ValueRef] }
}

enum VariableKind {
    ArgumentVariable(uint /*index*/),
    LocalVariable,
    CapturedVariable,
}

/// Create any deferred debug metadata nodes
pub fn finalize(cx: @mut CrateContext) {
    debug!("finalize");
    compile_unit_metadata(cx);
    unsafe {
        llvm::LLVMDIBuilderFinalize(DIB(cx));
        llvm::LLVMDIBuilderDispose(DIB(cx));
    };
}

/// Creates debug information for the given local variable.
///
/// Adds the created metadata nodes directly to the crate's IR.
pub fn create_local_var_metadata(bcx: @mut Block,
                                 local: &ast::Local) {
    if fn_should_be_ignored(bcx.fcx) {
        return;
    }

    let cx = bcx.ccx();
    let def_map = cx.tcx.def_map;

    do pat_util::pat_bindings(def_map, local.pat) |_, node_id, span, path_ref| {

        let var_ident = ast_util::path_to_ident(path_ref);
        let var_type = node_id_type(bcx, node_id);

        let llptr = match bcx.fcx.lllocals.find_copy(&node_id) {
            Some(v) => v,
            None => {
                bcx.tcx().sess.span_bug(span, fmt!("No entry in lllocals table for %?", node_id));
            }
        };

        let scope_metadata = scope_metadata(bcx.fcx, node_id, span);

        declare_local(bcx,
                      var_ident,
                      var_type,
                      scope_metadata,
                      DirectVariable { alloca: llptr },
                      LocalVariable,
                      span);
    }
}

/// Creates debug information for a variable captured in a closure.
///
/// Adds the created metadata nodes directly to the crate's IR.
pub fn create_captured_var_metadata(bcx: @mut Block,
                                    node_id: ast::NodeId,
                                    env_data_type: ty::t,
                                    env_pointer: ValueRef,
                                    env_index: uint,
                                    closure_sigil: ast::Sigil,
                                    span: Span) {
    if fn_should_be_ignored(bcx.fcx) {
        return;
    }

    let cx = bcx.ccx();

    let ast_item = cx.tcx.items.find_copy(&node_id);
    let variable_ident = match ast_item {
        None => {
            cx.sess.span_bug(span, "debuginfo::create_captured_var_metadata() - NodeId not found");
        }
        Some(ast_map::node_local(ident)) => ident,
        Some(ast_map::node_arg(@ast::Pat { node: ast::PatIdent(_, ref path, _), _ })) => {
            ast_util::path_to_ident(path)
        }
        _ => {
            cx.sess.span_bug(span, fmt!("debuginfo::create_captured_var_metadata() - \
                Captured var-id refers to unexpected ast_map variant: %?", ast_item));
        }
    };

    let variable_type = node_id_type(bcx, node_id);
    let scope_metadata = bcx.fcx.debug_context.get_ref(cx, span).fn_metadata;

    let llvm_env_data_type = type_of::type_of(cx, env_data_type);
    let byte_offset_of_var_in_env = machine::llelement_offset(cx, llvm_env_data_type, env_index);

    let address_operations = unsafe {
        [llvm::LLVMDIBuilderCreateOpDeref(Type::i64().to_ref()),
         llvm::LLVMDIBuilderCreateOpPlus(Type::i64().to_ref()),
         C_i64(byte_offset_of_var_in_env as i64),
         llvm::LLVMDIBuilderCreateOpDeref(Type::i64().to_ref())]
    };

    let address_op_count = match closure_sigil {
        ast::BorrowedSigil => {
            address_operations.len()
        }
        ast::ManagedSigil | ast::OwnedSigil => {
            address_operations.len() - 1
        }
    };

    let variable_access = IndirectVariable {
        alloca: env_pointer,
        address_operations: address_operations.slice_to(address_op_count)
    };

    declare_local(bcx,
                  variable_ident,
                  variable_type,
                  scope_metadata,
                  variable_access,
                  CapturedVariable,
                  span);
}

/// Creates debug information for a local variable introduced in the head of a match-statement arm.
///
/// Adds the created metadata nodes directly to the crate's IR.
pub fn create_match_binding_metadata(bcx: @mut Block,
                                     variable_ident: ast::Ident,
                                     node_id: ast::NodeId,
                                     variable_type: ty::t,
                                     span: Span) {
    if fn_should_be_ignored(bcx.fcx) {
        return;
    }

    let llptr = match bcx.fcx.lllocals.find_copy(&node_id) {
        Some(v) => v,
        None => {
            bcx.tcx().sess.span_bug(span, fmt!("No entry in lllocals table for %?", node_id));
        }
    };

    let scope_metadata = scope_metadata(bcx.fcx, node_id, span);

    declare_local(bcx,
                  variable_ident,
                  variable_type,
                  scope_metadata,
                  DirectVariable { alloca: llptr },
                  LocalVariable,
                  span);
}

/// Creates debug information for the self argument of a method.
///
/// Adds the created metadata nodes directly to the crate's IR.
pub fn create_self_argument_metadata(bcx: @mut Block,
                                     type_of_self: ty::t,
                                     llptr: ValueRef) {
    if fn_should_be_ignored(bcx.fcx) {
        return;
    }

    // Extract the span of the self argument from the method's AST
    let fnitem = bcx.ccx().tcx.items.get_copy(&bcx.fcx.id);
    let span = match fnitem {
        ast_map::node_method(@ast::method { explicit_self: explicit_self, _ }, _, _) => {
            explicit_self.span
        }
        ast_map::node_trait_method(
            @ast::provided(
                @ast::method {
                    explicit_self: explicit_self,
                    _
                }),
            _,
            _) => {
            explicit_self.span
        }
        _ => bcx.ccx().sess.bug(
                fmt!("create_self_argument_metadata: unexpected sort of node: %?", fnitem))
    };

    let scope_metadata = bcx.fcx.debug_context.get_ref(bcx.ccx(), span).fn_metadata;

    let argument_index = {
        let counter = &mut bcx.fcx.debug_context.get_mut_ref(bcx.ccx(), span).argument_counter;
        let argument_index = *counter;
        *counter += 1;
        argument_index
    };

    let address_operations = &[unsafe { llvm::LLVMDIBuilderCreateOpDeref(Type::i64().to_ref()) }];

    let variable_access = if unsafe { llvm::LLVMIsAAllocaInst(llptr) } != ptr::null() {
        DirectVariable { alloca: llptr }
    } else {
        // This is not stable and may break with future LLVM versions. llptr should really always
        // be an alloca. Anything else is not supported and just works by chance.
        IndirectVariable { alloca: llptr, address_operations: address_operations }
    };

    declare_local(bcx,
                  special_idents::self_,
                  type_of_self,
                  scope_metadata,
                  variable_access,
                  ArgumentVariable(argument_index),
                  span);
}

/// Creates debug information for the given function argument.
///
/// Adds the created metadata nodes directly to the crate's IR.
pub fn create_argument_metadata(bcx: @mut Block,
                                arg: &ast::arg) {
    if fn_should_be_ignored(bcx.fcx) {
        return;
    }

    let fcx = bcx.fcx;
    let cx = fcx.ccx;

    let def_map = cx.tcx.def_map;
    let scope_metadata = bcx.fcx.debug_context.get_ref(cx, arg.pat.span).fn_metadata;

    do pat_util::pat_bindings(def_map, arg.pat) |_, node_id, span, path_ref| {

        let llptr = match bcx.fcx.llargs.find_copy(&node_id) {
            Some(v) => v,
            None => {
                bcx.tcx().sess.span_bug(span, fmt!("No entry in llargs table for %?", node_id));
            }
        };

        if unsafe { llvm::LLVMIsAAllocaInst(llptr) } == ptr::null() {
            cx.sess.span_bug(span, "debuginfo::create_argument_metadata() - \
                                    Referenced variable location is not an alloca!");
        }

        let argument_type = node_id_type(bcx, node_id);
        let argument_ident = ast_util::path_to_ident(path_ref);

        let argument_index = {
            let counter = &mut fcx.debug_context.get_mut_ref(cx, span).argument_counter;
            let argument_index = *counter;
            *counter += 1;
            argument_index
        };

        declare_local(bcx,
                      argument_ident,
                      argument_type,
                      scope_metadata,
                      DirectVariable { alloca: llptr },
                      ArgumentVariable(argument_index),
                      span);
    }
}

/// Sets the current debug location at the beginning of the span.
///
/// Maps to a call to llvm::LLVMSetCurrentDebugLocation(...). The node_id parameter is used to
/// reliably find the correct visibility scope for the code position.
pub fn set_source_location(fcx: &FunctionContext,
                           node_id: ast::NodeId,
                           span: Span) {
    if fn_should_be_ignored(fcx) {
        return;
    }

    let cx = fcx.ccx;

    debug!("set_source_location: %s", cx.sess.codemap.span_to_str(span));

    if fcx.debug_context.get_ref(cx, span).source_locations_enabled {
        let loc = span_start(cx, span);
        let scope = scope_metadata(fcx, node_id, span);

        set_debug_location(cx, DebugLocation::new(scope, loc.line, *loc.col));
    } else {
        set_debug_location(cx, UnknownLocation);
    }
}

/// Enables emitting source locations for the given functions.
///
/// Since we don't want source locations to be emitted for the function prelude, they are disabled
/// when beginning to translate a new function. This functions switches source location emitting on
/// and must therefore be called before the first real statement/expression of the function is
/// translated.
pub fn start_emitting_source_locations(fcx: &mut FunctionContext) {
    match fcx.debug_context {
        FunctionDebugContext(~ref mut data) => data.source_locations_enabled = true,
        _ => { /* safe to ignore */ }
    }
}

/// Creates the function-specific debug context.
///
/// Returns the FunctionDebugContext for the function which holds state needed for debug info
/// creation. The function may also return another variant of the FunctionDebugContext enum which
/// indicates why no debuginfo should be created for the function.
pub fn create_function_debug_context(cx: &mut CrateContext,
                                     fn_ast_id: ast::NodeId,
                                     param_substs: Option<@param_substs>,
                                     llfn: ValueRef) -> FunctionDebugContext {
    if !cx.sess.opts.debuginfo {
        return DebugInfoDisabled;
    }

    if fn_ast_id == -1 {
        return FunctionWithoutDebugInfo;
    }

    let empty_generics = ast::Generics { lifetimes: opt_vec::Empty, ty_params: opt_vec::Empty };

    let fnitem = cx.tcx.items.get_copy(&fn_ast_id);
    let (ident, fn_decl, generics, top_level_block, span) = match fnitem {
        ast_map::node_item(ref item, _) => {
            match item.node {
                ast::item_fn(ref fn_decl, _, _, ref generics, ref top_level_block) => {
                    (item.ident, fn_decl, generics, Some(top_level_block), item.span)
                }
                _ => {
                    cx.sess.span_bug(item.span,
                        "create_function_debug_context: item bound to non-function");
                }
            }
        }
        ast_map::node_method(
            @ast::method {
                decl: ref fn_decl,
                ident: ident,
                generics: ref generics,
                body: ref top_level_block,
                span: span,
                _
            },
            _,
            _) => {
            (ident, fn_decl, generics, Some(top_level_block), span)
        }
        ast_map::node_expr(ref expr) => {
            match expr.node {
                ast::ExprFnBlock(ref fn_decl, ref top_level_block) => {
                    let name = fmt!("fn%u", token::gensym("fn"));
                    let name = token::str_to_ident(name);
                    (name, fn_decl,
                        // This is not quite right. It should actually inherit the generics of the
                        // enclosing function.
                        &empty_generics,
                        Some(top_level_block),
                        expr.span)
                }
                _ => cx.sess.span_bug(expr.span,
                        "create_function_debug_context: expected an expr_fn_block here")
            }
        }
        ast_map::node_trait_method(
            @ast::provided(
                @ast::method {
                    decl: ref fn_decl,
                    ident: ident,
                    generics: ref generics,
                    body: ref top_level_block,
                    span: span,
                    _
                }),
            _,
            _) => {
            (ident, fn_decl, generics, Some(top_level_block), span)
        }
        ast_map::node_foreign_item(@ast::foreign_item {
                ident: ident,
                node: ast::foreign_item_fn(ref fn_decl, ref generics),
                span: span,
                _
            },
            _,
            _,
            _) => {
            (ident, fn_decl, generics, None, span)
        }
        ast_map::node_variant(*)     |
        ast_map::node_struct_ctor(*) => {
            return FunctionWithoutDebugInfo;
        }
        _ => cx.sess.bug(fmt!("create_function_debug_context: unexpected sort of node: %?", fnitem))
    };

    // This can be the case for functions inlined from another crate
    if span == codemap::dummy_sp() {
        return FunctionWithoutDebugInfo;
    }

    let loc = span_start(cx, span);
    let file_metadata = file_metadata(cx, loc.file.name);

    let function_type_metadata = unsafe {
        let fn_signature = get_function_signature(cx, fn_ast_id, fn_decl, param_substs);
        llvm::LLVMDIBuilderCreateSubroutineType(DIB(cx), file_metadata, fn_signature)
    };

    // get_template_parameters() will append a `<...>` clause to the function name if necessary.
    let mut function_name = cx.sess.str_of(ident).to_owned();
    let template_parameters = if cx.sess.opts.extra_debuginfo {
        get_template_parameters(cx, generics, param_substs, file_metadata, &mut function_name)
    } else {
        ptr::null()
    };

    let scope_line = get_scope_line(cx, top_level_block, loc.line);

    let fn_metadata = do function_name.to_c_str().with_ref |function_name| {
        unsafe {
            llvm::LLVMDIBuilderCreateFunction(
                DIB(cx),
                file_metadata,
                function_name,
                function_name,
                file_metadata,
                loc.line as c_uint,
                function_type_metadata,
                false,
                true,
                scope_line as c_uint,
                FlagPrototyped as c_uint,
                cx.sess.opts.optimize != session::No,
                llfn,
                template_parameters,
                ptr::null())
        }
    };

    // Initialize fn debug context (including scope map)
    let mut fn_debug_context = ~FunctionDebugContextData {
        scope_map: HashMap::new(),
        fn_metadata: fn_metadata,
        argument_counter: 1,
        source_locations_enabled: false,
    };

    let arg_pats = do fn_decl.inputs.map |arg_ref| { arg_ref.pat };
    populate_scope_map(cx, arg_pats, top_level_block, fn_metadata, &mut fn_debug_context.scope_map);

    return FunctionDebugContext(fn_debug_context);

    fn get_function_signature(cx: &mut CrateContext,
                              fn_ast_id: ast::NodeId,
                              fn_decl: &ast::fn_decl,
                              param_substs: Option<@param_substs>) -> DIArray {
        if !cx.sess.opts.extra_debuginfo {
            return create_DIArray(DIB(cx), []);
        }

        let mut signature = vec::with_capacity(fn_decl.inputs.len() + 1);

        // Return type -- llvm::DIBuilder wants this at index 0
        match fn_decl.output.node {
            ast::ty_nil => {
                signature.push(ptr::null());
            }
            _ => {
                let return_type = ty::node_id_to_type(cx.tcx, fn_ast_id);
                let return_type = match param_substs {
                    None => return_type,
                    Some(substs) => {
                        ty::subst_tps(cx.tcx, substs.tys, substs.self_ty, return_type)
                    }
                };

                signature.push(type_metadata(cx, return_type, codemap::dummy_sp()));
            }
        }

        // arguments types
        for arg in fn_decl.inputs.iter() {
            let arg_type = ty::node_id_to_type(cx.tcx, arg.pat.id);
            let arg_type = match param_substs {
                None => arg_type,
                Some(substs) => {
                    ty::subst_tps(cx.tcx, substs.tys, substs.self_ty, arg_type)
                }
            };

            signature.push(type_metadata(cx, arg_type, codemap::dummy_sp()));
        }

        return create_DIArray(DIB(cx), signature);
    }

    fn get_template_parameters(cx: &mut CrateContext,
                               generics: &ast::Generics,
                               param_substs: Option<@param_substs>,
                               file_metadata: DIFile,
                               name_to_append_suffix_to: &mut ~str)
                            -> DIArray {
        let self_type = match param_substs {
            Some(@param_substs{ self_ty: self_type, _ }) => self_type,
            _ => None
        };

        // Only true for static default methods:
        let has_self_type = self_type.is_some();

        if !generics.is_type_parameterized() && !has_self_type {
            return ptr::null();
        }

        name_to_append_suffix_to.push_char('<');

        // The list to be filled with template parameters:
        let mut template_params: ~[DIDescriptor] = vec::with_capacity(generics.ty_params.len() + 1);

        // Handle self type
        if has_self_type {
            let actual_self_type = self_type.unwrap();
            let actual_self_type_metadata = type_metadata(cx,
                                                          actual_self_type,
                                                          codemap::dummy_sp());

            // Add self type name to <...> clause of function name
            let actual_self_type_name = ty_to_str(cx.tcx, actual_self_type);
            name_to_append_suffix_to.push_str(actual_self_type_name);
            if generics.is_type_parameterized() {
                name_to_append_suffix_to.push_str(",");
            }

            let ident = special_idents::type_self;

            let param_metadata = do cx.sess.str_of(ident).to_c_str().with_ref |name| {
                unsafe {
                    llvm::LLVMDIBuilderCreateTemplateTypeParameter(
                        DIB(cx),
                        file_metadata,
                        name,
                        actual_self_type_metadata,
                        ptr::null(),
                        0,
                        0)
                }
            };

            template_params.push(param_metadata);
        }

        // Handle other generic parameters
        let actual_types = match param_substs {
            Some(@param_substs { tys: ref types, _ }) => types,
            None => {
                return create_DIArray(DIB(cx), template_params);
            }
        };

        for (index, &ast::TyParam{ ident: ident, _ }) in generics.ty_params.iter().enumerate() {
            let actual_type = actual_types[index];
            let actual_type_metadata = type_metadata(cx, actual_type, codemap::dummy_sp());

            // Add actual type name to <...> clause of function name
            let actual_type_name = ty_to_str(cx.tcx, actual_type);
            name_to_append_suffix_to.push_str(actual_type_name);

            if index != generics.ty_params.len() - 1 {
                name_to_append_suffix_to.push_str(",");
            }

            let param_metadata = do cx.sess.str_of(ident).to_c_str().with_ref |name| {
                unsafe {
                    llvm::LLVMDIBuilderCreateTemplateTypeParameter(
                        DIB(cx),
                        file_metadata,
                        name,
                        actual_type_metadata,
                        ptr::null(),
                        0,
                        0)
                }
            };

            template_params.push(param_metadata);
        }

        name_to_append_suffix_to.push_char('>');

        return create_DIArray(DIB(cx), template_params);
    }

    fn get_scope_line(cx: &CrateContext,
                      top_level_block: Option<&ast::Block>,
                      default: uint)
                   -> uint {
        match top_level_block {
            Some(&ast::Block { stmts: ref statements, _ }) if statements.len() > 0 => {
                span_start(cx, statements[0].span).line
            }
            Some(&ast::Block { expr: Some(@ref expr), _ }) => {
                span_start(cx, expr.span).line
            }
            _ => default
        }
    }
}

//=-------------------------------------------------------------------------------------------------
// Module-Internal debug info creation functions
//=-------------------------------------------------------------------------------------------------

fn create_DIArray(builder: DIBuilderRef, arr: &[DIDescriptor]) -> DIArray {
    return unsafe {
        llvm::LLVMDIBuilderGetOrCreateArray(builder, vec::raw::to_ptr(arr), arr.len() as u32)
    };
}

fn compile_unit_metadata(cx: @mut CrateContext) {
    let dcx = dbg_cx(cx);
    let crate_name: &str = dcx.crate_file;

    debug!("compile_unit_metadata: %?", crate_name);

    let work_dir = cx.sess.working_dir.to_str();
    let producer = fmt!("rustc version %s", env!("CFG_VERSION"));

    do crate_name.with_c_str |crate_name| {
    do work_dir.with_c_str |work_dir| {
    do producer.with_c_str |producer| {
    do "".with_c_str |flags| {
    do "".with_c_str |split_name| {
        unsafe {
            llvm::LLVMDIBuilderCreateCompileUnit(
                dcx.builder,
                DW_LANG_RUST,
                crate_name,
                work_dir,
                producer,
                cx.sess.opts.optimize != session::No,
                flags,
                0,
                split_name);
        }
    }}}}};
}

fn declare_local(bcx: @mut Block,
                 variable_ident: ast::Ident,
                 variable_type: ty::t,
                 scope_metadata: DIScope,
                 variable_access: VariableAccess,
                 variable_kind: VariableKind,
                 span: Span) {
    let cx: &mut CrateContext = bcx.ccx();

    let filename = span_start(cx, span).file.name;
    let file_metadata = file_metadata(cx, filename);

    let name: &str = cx.sess.str_of(variable_ident);
    let loc = span_start(cx, span);
    let type_metadata = type_metadata(cx, variable_type, span);

    let argument_index = match variable_kind {
        ArgumentVariable(index) => index,
        LocalVariable    |
        CapturedVariable => 0
    } as c_uint;

    let (var_alloca, var_metadata) = do name.with_c_str |name| {
        match variable_access {
            DirectVariable { alloca } => (
                alloca,
                unsafe {
                    llvm::LLVMDIBuilderCreateLocalVariable(
                        DIB(cx),
                        DW_TAG_auto_variable,
                        scope_metadata,
                        name,
                        file_metadata,
                        loc.line as c_uint,
                        type_metadata,
                        cx.sess.opts.optimize != session::No,
                        0,
                        argument_index)
                }
            ),
            IndirectVariable { alloca, address_operations } => (
                alloca,
                unsafe {
                    llvm::LLVMDIBuilderCreateComplexVariable(
                        DIB(cx),
                        DW_TAG_auto_variable,
                        scope_metadata,
                        name,
                        file_metadata,
                        loc.line as c_uint,
                        type_metadata,
                        vec::raw::to_ptr(address_operations),
                        address_operations.len() as c_uint,
                        argument_index)
                }
            )
        }
    };

    set_debug_location(cx, DebugLocation::new(scope_metadata, loc.line, *loc.col));
    unsafe {
        let instr = llvm::LLVMDIBuilderInsertDeclareAtEnd(
            DIB(cx),
            var_alloca,
            var_metadata,
            bcx.llbb);

        llvm::LLVMSetInstDebugLocation(trans::build::B(bcx).llbuilder, instr);
    }

    match variable_kind {
        ArgumentVariable(_) | CapturedVariable => {
            assert!(!bcx.fcx.debug_context.get_ref(cx, span).source_locations_enabled);
            set_debug_location(cx, UnknownLocation);
        }
        _ => { /* fallthrough */ }
    }
}

fn file_metadata(cx: &mut CrateContext, full_path: &str) -> DIFile {
    match dbg_cx(cx).created_files.find_equiv(&full_path) {
        Some(file_metadata) => return *file_metadata,
        None => ()
    }

    debug!("file_metadata: %s", full_path);

    let work_dir = cx.sess.working_dir.to_str();
    let file_name =
        if full_path.starts_with(work_dir) {
            full_path.slice(work_dir.len() + 1u, full_path.len())
        } else {
            full_path
        };

    let file_metadata =
        do file_name.with_c_str |file_name| {
        do work_dir.with_c_str |work_dir| {
            unsafe {
                llvm::LLVMDIBuilderCreateFile(DIB(cx), file_name, work_dir)
            }
        }};

    dbg_cx(cx).created_files.insert(full_path.to_owned(), file_metadata);
    return file_metadata;
}

/// Finds the scope metadata node for the given AST node.
fn scope_metadata(fcx: &FunctionContext,
                  node_id: ast::NodeId,
                  span: Span)
               -> DIScope {
    let scope_map = &fcx.debug_context.get_ref(fcx.ccx, span).scope_map;

    match scope_map.find_copy(&node_id) {
        Some(scope_metadata) => scope_metadata,
        None => {
            let node = fcx.ccx.tcx.items.get_copy(&node_id);

            fcx.ccx.sess.span_bug(span,
                fmt!("debuginfo: Could not find scope info for node %?", node));
        }
    }
}

fn basic_type_metadata(cx: &mut CrateContext, t: ty::t) -> DIType {

    debug!("basic_type_metadata: %?", ty::get(t));

    let (name, encoding) = match ty::get(t).sty {
        ty::ty_nil | ty::ty_bot => (~"uint", DW_ATE_unsigned),
        ty::ty_bool => (~"bool", DW_ATE_boolean),
        ty::ty_char => (~"char", DW_ATE_unsigned_char),
        ty::ty_int(int_ty) => match int_ty {
            ast::ty_i => (~"int", DW_ATE_signed),
            ast::ty_i8 => (~"i8", DW_ATE_signed),
            ast::ty_i16 => (~"i16", DW_ATE_signed),
            ast::ty_i32 => (~"i32", DW_ATE_signed),
            ast::ty_i64 => (~"i64", DW_ATE_signed)
        },
        ty::ty_uint(uint_ty) => match uint_ty {
            ast::ty_u => (~"uint", DW_ATE_unsigned),
            ast::ty_u8 => (~"u8", DW_ATE_unsigned),
            ast::ty_u16 => (~"u16", DW_ATE_unsigned),
            ast::ty_u32 => (~"u32", DW_ATE_unsigned),
            ast::ty_u64 => (~"u64", DW_ATE_unsigned)
        },
        ty::ty_float(float_ty) => match float_ty {
            ast::ty_f => (~"float", DW_ATE_float),
            ast::ty_f32 => (~"f32", DW_ATE_float),
            ast::ty_f64 => (~"f64", DW_ATE_float)
        },
        _ => cx.sess.bug("debuginfo::basic_type_metadata - t is invalid type")
    };

    let llvm_type = type_of::type_of(cx, t);
    let (size, align) = size_and_align_of(cx, llvm_type);
    let ty_metadata = do name.with_c_str |name| {
        unsafe {
            llvm::LLVMDIBuilderCreateBasicType(
                DIB(cx),
                name,
                bytes_to_bits(size),
                bytes_to_bits(align),
                encoding)
        }
    };

    return ty_metadata;
}

fn pointer_type_metadata(cx: &mut CrateContext,
                         pointer_type: ty::t,
                         pointee_type_metadata: DIType)
                      -> DIType {
    let pointer_llvm_type = type_of::type_of(cx, pointer_type);
    let (pointer_size, pointer_align) = size_and_align_of(cx, pointer_llvm_type);
    let name = ty_to_str(cx.tcx, pointer_type);
    let ptr_metadata = do name.with_c_str |name| {
        unsafe {
            llvm::LLVMDIBuilderCreatePointerType(
                DIB(cx),
                pointee_type_metadata,
                bytes_to_bits(pointer_size),
                bytes_to_bits(pointer_align),
                name)
        }
    };
    return ptr_metadata;
}

fn struct_metadata(cx: &mut CrateContext,
                   struct_type: ty::t,
                   fields: ~[ty::field],
                   span: Span)
                -> DICompositeType {
    let struct_name = ty_to_str(cx.tcx, struct_type);
    debug!("struct_metadata: %s", struct_name);

    let struct_llvm_type = type_of::type_of(cx, struct_type);

    let field_llvm_types = do fields.map |field| { type_of::type_of(cx, field.mt.ty) };
    let field_names = do fields.map |field| {
        if field.ident.name == special_idents::unnamed_field.name {
            ~""
        } else {
            cx.sess.str_of(field.ident).to_owned()
        }
    };
    let field_types_metadata = do fields.map |field| {
        type_metadata(cx, field.mt.ty, span)
    };

    return composite_type_metadata(
        cx,
        struct_llvm_type,
        struct_name,
        field_llvm_types,
        field_names,
        field_types_metadata,
        span);
}

fn tuple_metadata(cx: &mut CrateContext,
                  tuple_type: ty::t,
                  component_types: &[ty::t],
                  span: Span)
               -> DICompositeType {

    let tuple_name = ty_to_str(cx.tcx, tuple_type);
    let tuple_llvm_type = type_of::type_of(cx, tuple_type);

    let component_names = do component_types.map |_| { ~"" };
    let component_llvm_types = do component_types.map |it| { type_of::type_of(cx, *it) };
    let component_types_metadata = do component_types.map |it| {
        type_metadata(cx, *it, span)
    };

    return composite_type_metadata(
        cx,
        tuple_llvm_type,
        tuple_name,
        component_llvm_types,
        component_names,
        component_types_metadata,
        span);
}

fn enum_metadata(cx: &mut CrateContext,
                 enum_type: ty::t,
                 enum_def_id: ast::DefId,
                 span: Span)
              -> DIType {

    let enum_name = ty_to_str(cx.tcx, enum_type);

    // For empty enums there is an early exit. Just describe it as an empty struct with the
    // appropriate type name
    if ty::type_is_empty(cx.tcx, enum_type) {
        return composite_type_metadata(cx, Type::nil(), enum_name, [], [], [], span);
    }

    // Prepare some data (llvm type, size, align, ...) about the discriminant. This data will be
    // needed in all of the following cases.
    let discriminant_llvm_type = Type::enum_discrim(cx);
    let (discriminant_size, discriminant_align) = size_and_align_of(cx, discriminant_llvm_type);

    assert!(Type::enum_discrim(cx) == cx.int_type);
    let discriminant_type_metadata = type_metadata(cx, ty::mk_int(), span);

    let variants: &[@ty::VariantInfo] = *ty::enum_variants(cx.tcx, enum_def_id);

    let enumerators_metadata: ~[DIDescriptor] = variants
        .iter()
        .map(|v| {
            let name: &str = cx.sess.str_of(v.name);
            let discriminant_value = v.disr_val as c_ulonglong;

            do name.with_c_str |name| {
                unsafe {
                    llvm::LLVMDIBuilderCreateEnumerator(
                        DIB(cx),
                        name,
                        discriminant_value)
                }
            }
        })
        .collect();

    let loc = span_start(cx, span);
    let file_metadata = file_metadata(cx, loc.file.name);

    let discriminant_type_metadata = do enum_name.with_c_str |enum_name| {
        unsafe {
            llvm::LLVMDIBuilderCreateEnumerationType(
                DIB(cx),
                file_metadata,
                enum_name,
                file_metadata,
                loc.line as c_uint,
                bytes_to_bits(discriminant_size),
                bytes_to_bits(discriminant_align),
                create_DIArray(DIB(cx), enumerators_metadata),
                discriminant_type_metadata)
        }
    };

    let type_rep = adt::represent_type(cx, enum_type);

    match *type_rep {
        adt::CEnum(*) => {
            return discriminant_type_metadata;
        }
        adt::Univariant(ref struct_def, _) => {
            assert!(variants.len() == 1);
            return adt_struct_metadata(cx, struct_def, variants[0], None, span);
        }
        adt::General(ref struct_defs) => {
            let variants_member_metadata: ~[DIDescriptor] = do struct_defs
                .iter()
                .enumerate()
                .map |(i, struct_def)| {
                    let variant_type_metadata = adt_struct_metadata(
                        cx,
                        struct_def,
                        variants[i],
                        Some(discriminant_type_metadata),
                        span);

                    do "".with_c_str |name| {
                        unsafe {
                            llvm::LLVMDIBuilderCreateMemberType(
                                DIB(cx),
                                file_metadata,
                                name,
                                file_metadata,
                                loc.line as c_uint,
                                bytes_to_bits(struct_def.size as uint),
                                bytes_to_bits(struct_def.align as uint),
                                bytes_to_bits(0),
                                0,
                                variant_type_metadata)
                        }
                    }
            }.collect();

            let enum_llvm_type = type_of::type_of(cx, enum_type);
            let (enum_type_size, enum_type_align) = size_and_align_of(cx, enum_llvm_type);

            return do enum_name.with_c_str |enum_name| {
                unsafe {
                    llvm::LLVMDIBuilderCreateUnionType(
                    DIB(cx),
                    file_metadata,
                    enum_name,
                    file_metadata,
                    loc.line as c_uint,
                    bytes_to_bits(enum_type_size),
                    bytes_to_bits(enum_type_align),
                    0, // Flags
                    create_DIArray(DIB(cx), variants_member_metadata),
                    0) // RuntimeLang
            }};
        }
        adt::NullablePointer { nonnull: ref struct_def, nndiscr, _ } => {
            return adt_struct_metadata(cx, struct_def, variants[nndiscr], None, span);
        }
    }

    fn adt_struct_metadata(cx: &mut CrateContext,
                                  struct_def: &adt::Struct,
                                  variant_info: &ty::VariantInfo,
                                  discriminant_type_metadata: Option<DIType>,
                                  span: Span)
                               -> DICompositeType
    {
        let arg_llvm_types: ~[Type] = do struct_def.fields.map |&ty| { type_of::type_of(cx, ty) };
        let arg_metadata: ~[DIType] = do struct_def.fields.iter().enumerate()
            .map |(i, &ty)| {
                match discriminant_type_metadata {
                    Some(metadata) if i == 0 => metadata,
                    _                        => type_metadata(cx, ty, span)
                }
        }.collect();

        let mut arg_names = match variant_info.arg_names {
            Some(ref names) => do names.map |ident| { cx.sess.str_of(*ident).to_owned() },
            None => do variant_info.args.map |_| { ~"" }
        };

        if discriminant_type_metadata.is_some() {
            arg_names.insert(0, ~"");
        }

        let variant_llvm_type = Type::struct_(arg_llvm_types, struct_def.packed);
        let variant_name: &str = cx.sess.str_of(variant_info.name);

        return composite_type_metadata(
            cx,
            variant_llvm_type,
            variant_name,
            arg_llvm_types,
            arg_names,
            arg_metadata,
            span);
    }
}

/// Creates debug information for a composite type, that is, anything that results in a LLVM struct.
///
/// Examples of Rust types to use this are: structs, tuples, boxes, vecs, and enums.
fn composite_type_metadata(cx: &mut CrateContext,
                           composite_llvm_type: Type,
                           composite_type_name: &str,
                           member_llvm_types: &[Type],
                           member_names: &[~str],
                           member_type_metadata: &[DIType],
                           span: Span)
                        -> DICompositeType {

    let loc = span_start(cx, span);
    let file_metadata = file_metadata(cx, loc.file.name);

    let (composite_size, composite_align) = size_and_align_of(cx, composite_llvm_type);

    let member_metadata: ~[DIDescriptor] = member_llvm_types
        .iter()
        .enumerate()
        .map(|(i, &member_llvm_type)| {
            let (member_size, member_align) = size_and_align_of(cx, member_llvm_type);
            let member_offset = machine::llelement_offset(cx, composite_llvm_type, i);
            let member_name: &str = member_names[i];

            do member_name.with_c_str |member_name| {
                unsafe {
                    llvm::LLVMDIBuilderCreateMemberType(
                        DIB(cx),
                        file_metadata,
                        member_name,
                        file_metadata,
                        loc.line as c_uint,
                        bytes_to_bits(member_size),
                        bytes_to_bits(member_align),
                        bytes_to_bits(member_offset),
                        0,
                        member_type_metadata[i])
                }
            }
        })
        .collect();

    return do composite_type_name.with_c_str |name| {
        unsafe {
            llvm::LLVMDIBuilderCreateStructType(
                DIB(cx),
                file_metadata,
                name,
                file_metadata,
                loc.line as c_uint,
                bytes_to_bits(composite_size),
                bytes_to_bits(composite_align),
                0,
                ptr::null(),
                create_DIArray(DIB(cx), member_metadata),
                0,
                ptr::null())
    }
    };
}

fn boxed_type_metadata(cx: &mut CrateContext,
                       content_type_name: Option<&str>,
                       content_llvm_type: Type,
                       content_type_metadata: DIType,
                       span: Span)
                    -> DICompositeType {

    let box_type_name = match content_type_name {
        Some(content_type_name) => fmt!("Boxed<%s>", content_type_name),
        None                    => ~"BoxedType"
    };

    let box_llvm_type = Type::box(cx, &content_llvm_type);
    let member_llvm_types = box_llvm_type.field_types();
    let member_names = [~"refcnt", ~"tydesc", ~"prev", ~"next", ~"val"];

    assert!(box_layout_is_correct(cx, member_llvm_types, content_llvm_type));

    let int_type = ty::mk_int();
    let nil_pointer_type = ty::mk_nil_ptr(cx.tcx);

    let member_types_metadata = [
        type_metadata(cx, int_type, span),
        type_metadata(cx, nil_pointer_type, span),
        type_metadata(cx, nil_pointer_type, span),
        type_metadata(cx, nil_pointer_type, span),
        content_type_metadata
    ];

    return composite_type_metadata(
        cx,
        box_llvm_type,
        box_type_name,
        member_llvm_types,
        member_names,
        member_types_metadata,
        span);

    // Unfortunately, we cannot assert anything but the correct types here---and not whether the
    // 'next' and 'prev' pointers are in the correct order.
    fn box_layout_is_correct(cx: &CrateContext,
                             member_llvm_types: &[Type],
                             content_llvm_type: Type)
                          -> bool {
        member_llvm_types.len() == 5 &&
        member_llvm_types[0] == cx.int_type &&
        member_llvm_types[1] == cx.tydesc_type.ptr_to() &&
        member_llvm_types[2] == Type::i8().ptr_to() &&
        member_llvm_types[3] == Type::i8().ptr_to() &&
        member_llvm_types[4] == content_llvm_type
    }
}

fn fixed_vec_metadata(cx: &mut CrateContext,
                      element_type: ty::t,
                      len: uint,
                      span: Span)
                   -> DIType {
    let element_type_metadata = type_metadata(cx, element_type, span);
    let element_llvm_type = type_of::type_of(cx, element_type);
    let (element_type_size, element_type_align) = size_and_align_of(cx, element_llvm_type);

    let subrange = unsafe {
        llvm::LLVMDIBuilderGetOrCreateSubrange(
        DIB(cx),
        0,
        len as c_longlong)
    };

    let subscripts = create_DIArray(DIB(cx), [subrange]);
    return unsafe {
        llvm::LLVMDIBuilderCreateArrayType(
            DIB(cx),
            bytes_to_bits(element_type_size * len),
            bytes_to_bits(element_type_align),
            element_type_metadata,
            subscripts)
    };
}

fn vec_metadata(cx: &mut CrateContext,
                element_type: ty::t,
                span: Span)
             -> DICompositeType {

    let element_type_metadata = type_metadata(cx, element_type, span);
    let element_llvm_type = type_of::type_of(cx, element_type);
    let (element_size, element_align) = size_and_align_of(cx, element_llvm_type);

    let vec_llvm_type = Type::vec(cx.sess.targ_cfg.arch, &element_llvm_type);
    let vec_type_name: &str = fmt!("[%s]", ty_to_str(cx.tcx, element_type));

    let member_llvm_types = vec_llvm_type.field_types();
    let member_names = &[~"fill", ~"alloc", ~"elements"];

    let int_type_metadata = type_metadata(cx, ty::mk_int(), span);
    let array_type_metadata = unsafe {
        llvm::LLVMDIBuilderCreateArrayType(
            DIB(cx),
            bytes_to_bits(element_size),
            bytes_to_bits(element_align),
            element_type_metadata,
            create_DIArray(DIB(cx), [llvm::LLVMDIBuilderGetOrCreateSubrange(DIB(cx), 0, 0)]))
    };

    //                           fill               alloc              elements
    let member_type_metadata = &[int_type_metadata, int_type_metadata, array_type_metadata];

    return composite_type_metadata(
        cx,
        vec_llvm_type,
        vec_type_name,
        member_llvm_types,
        member_names,
        member_type_metadata,
        span);
}

fn boxed_vec_metadata(cx: &mut CrateContext,
                      element_type: ty::t,
                      span: Span)
                   -> DICompositeType {

    let element_llvm_type = type_of::type_of(cx, element_type);
    let vec_llvm_type = Type::vec(cx.sess.targ_cfg.arch, &element_llvm_type);
    let vec_type_name: &str = fmt!("[%s]", ty_to_str(cx.tcx, element_type));
    let vec_metadata = vec_metadata(cx, element_type, span);

    return boxed_type_metadata(
        cx,
        Some(vec_type_name),
        vec_llvm_type,
        vec_metadata,
        span);
}

fn vec_slice_metadata(cx: &mut CrateContext,
                      vec_type: ty::t,
                      element_type: ty::t,
                      span: Span)
                   -> DICompositeType {

    debug!("vec_slice_metadata: %?", ty::get(vec_type));

    let slice_llvm_type = type_of::type_of(cx, vec_type);
    let slice_type_name = ty_to_str(cx.tcx, vec_type);

    let member_llvm_types = slice_llvm_type.field_types();
    let member_names = &[~"data_ptr", ~"size_in_bytes"];

    assert!(slice_layout_is_correct(cx, member_llvm_types, element_type));

    let data_ptr_type = ty::mk_ptr(cx.tcx, ty::mt { ty: element_type, mutbl: ast::MutImmutable });

    let member_type_metadata = &[type_metadata(cx, data_ptr_type, span),
                                 type_metadata(cx, ty::mk_uint(), span)];

    return composite_type_metadata(
        cx,
        slice_llvm_type,
        slice_type_name,
        member_llvm_types,
        member_names,
        member_type_metadata,
        span);

    fn slice_layout_is_correct(cx: &mut CrateContext,
                               member_llvm_types: &[Type],
                               element_type: ty::t)
                            -> bool {
        member_llvm_types.len() == 2 &&
        member_llvm_types[0] == type_of::type_of(cx, element_type).ptr_to() &&
        member_llvm_types[1] == cx.int_type
    }
}

fn subroutine_type_metadata(cx: &mut CrateContext,
                            signature: &ty::FnSig,
                            span: Span)
                         -> DICompositeType {
    let loc = span_start(cx, span);
    let file_metadata = file_metadata(cx, loc.file.name);

    let mut signature_metadata: ~[DIType] = vec::with_capacity(signature.inputs.len() + 1);

    // return type
    signature_metadata.push(match ty::get(signature.output).sty {
        ty::ty_nil => ptr::null(),
        _ => type_metadata(cx, signature.output, span)
    });

    // regular arguments
    for &argument_type in signature.inputs.iter() {
        signature_metadata.push(type_metadata(cx, argument_type, span));
    }

    return unsafe {
        llvm::LLVMDIBuilderCreateSubroutineType(
            DIB(cx),
            file_metadata,
            create_DIArray(DIB(cx), signature_metadata))
    };
}

fn unimplemented_type_metadata(cx: &mut CrateContext, t: ty::t) -> DIType {
    debug!("unimplemented_type_metadata: %?", ty::get(t));

    let name = ty_to_str(cx.tcx, t);
    let metadata = do fmt!("NYI<%s>", name).with_c_str |name| {
        unsafe {
            llvm::LLVMDIBuilderCreateBasicType(
                DIB(cx),
                name,
                0_u64,
                8_u64,
                DW_ATE_unsigned as c_uint)
            }
        };

    return metadata;
}

fn type_metadata(cx: &mut CrateContext,
                 t: ty::t,
                 span: Span)
              -> DIType {
    let type_id = ty::type_id(t);
    match dbg_cx(cx).created_types.find(&type_id) {
        Some(type_metadata) => return *type_metadata,
        None => ()
    }

    fn create_pointer_to_box_metadata(cx: &mut CrateContext,
                                      pointer_type: ty::t,
                                      type_in_box: ty::t)
                                   -> DIType {

        let content_type_name: &str = ty_to_str(cx.tcx, type_in_box);
        let content_llvm_type = type_of::type_of(cx, type_in_box);
        let content_type_metadata = type_metadata(
            cx,
            type_in_box,
            codemap::dummy_sp());

        let box_metadata = boxed_type_metadata(
            cx,
            Some(content_type_name),
            content_llvm_type,
            content_type_metadata,
            codemap::dummy_sp());

        pointer_type_metadata(cx, pointer_type, box_metadata)
    }

    debug!("type_metadata: %?", ty::get(t));

    let sty = &ty::get(t).sty;
    let type_metadata = match *sty {
        ty::ty_nil      |
        ty::ty_bot      |
        ty::ty_bool     |
        ty::ty_char     |
        ty::ty_int(_)   |
        ty::ty_uint(_)  |
        ty::ty_float(_) => {
            basic_type_metadata(cx, t)
        },
        ty::ty_estr(ref vstore) => {
            let i8_t = ty::mk_i8();
            match *vstore {
                ty::vstore_fixed(len) => {
                    fixed_vec_metadata(cx, i8_t, len + 1, span)
                },
                ty::vstore_uniq  => {
                    let vec_metadata = vec_metadata(cx, i8_t, span);
                    pointer_type_metadata(cx, t, vec_metadata)
                }
                ty::vstore_box => {
                    let boxed_vec_metadata = boxed_vec_metadata(cx, i8_t, span);
                    pointer_type_metadata(cx, t, boxed_vec_metadata)
                }
                ty::vstore_slice(_region) => {
                    vec_slice_metadata(cx, t, i8_t, span)
                }
            }
        },
        ty::ty_enum(def_id, _) => {
            enum_metadata(cx, t, def_id, span)
        },
        ty::ty_box(ref mt) => {
            create_pointer_to_box_metadata(cx, t, mt.ty)
        },
        ty::ty_evec(ref mt, ref vstore) => {
            match *vstore {
                ty::vstore_fixed(len) => {
                    fixed_vec_metadata(cx, mt.ty, len, span)
                }
                ty::vstore_uniq if ty::type_contents(cx.tcx, mt.ty).contains_managed() => {
                    let boxed_vec_metadata = boxed_vec_metadata(cx, mt.ty, span);
                    pointer_type_metadata(cx, t, boxed_vec_metadata)
                }
                ty::vstore_uniq => {
                    let vec_metadata = vec_metadata(cx, mt.ty, span);
                    pointer_type_metadata(cx, t, vec_metadata)
                }
                ty::vstore_box => {
                    let boxed_vec_metadata = boxed_vec_metadata(cx, mt.ty, span);
                    pointer_type_metadata(cx, t, boxed_vec_metadata)
                }
                ty::vstore_slice(_) => {
                    vec_slice_metadata(cx, t, mt.ty, span)
                }
            }
        },
        ty::ty_uniq(ref mt) if ty::type_contents(cx.tcx, mt.ty).contains_managed() => {
            create_pointer_to_box_metadata(cx, t, mt.ty)
        },
        ty::ty_uniq(ref mt)    |
        ty::ty_ptr(ref mt)     |
        ty::ty_rptr(_, ref mt) => {
            let pointee = type_metadata(cx, mt.ty, span);
            pointer_type_metadata(cx, t, pointee)
        },
        ty::ty_bare_fn(ref barefnty) => {
            subroutine_type_metadata(cx, &barefnty.sig, span)
        },
        ty::ty_closure(ref closurety) => {
            subroutine_type_metadata(cx, &closurety.sig, span)
        },
        ty::ty_trait(_did, ref _substs, ref _vstore, _, _bounds) => {
            cx.sess.span_note(span, "debuginfo for trait NYI");
            unimplemented_type_metadata(cx, t)
        },
        ty::ty_struct(did, ref substs) => {
            let fields = ty::struct_fields(cx.tcx, did, substs);
            struct_metadata(cx, t, fields, span)
        },
        ty::ty_tup(ref elements) => {
            tuple_metadata(cx, t, *elements, span)
        },
        ty::ty_opaque_box => {
            cx.sess.span_note(span, "debuginfo for ty_opaque_box NYI");
            unimplemented_type_metadata(cx, t)
        }
        _ => cx.sess.bug(fmt!("debuginfo: unexpected type in type_metadata: %?", sty))
    };

    dbg_cx(cx).created_types.insert(type_id, type_metadata);
    return type_metadata;
}

#[deriving(Eq)]
enum DebugLocation {
    KnownLocation { scope: DIScope, line: uint, col: uint },
    UnknownLocation
}

impl DebugLocation {
    fn new(scope: DIScope, line: uint, col: uint) -> DebugLocation {
        KnownLocation {
            scope: scope,
            line: line,
            col: col,
        }
    }
}

fn set_debug_location(cx: &mut CrateContext, debug_location: DebugLocation) {
    if debug_location == dbg_cx(cx).curr_loc {
        return;
    }

    let metadata_node;

    match debug_location {
        KnownLocation { scope, line, col } => {
            debug!("setting debug location to %u %u", line, col);
            let elements = [C_i32(line as i32), C_i32(col as i32), scope, ptr::null()];
            unsafe {
                metadata_node = llvm::LLVMMDNodeInContext(dbg_cx(cx).llcontext,
                                                          vec::raw::to_ptr(elements),
                                                          elements.len() as c_uint);
            }
        }
        UnknownLocation => {
            debug!("clearing debug location ");
            metadata_node = ptr::null();
        }
    };

    unsafe {
        llvm::LLVMSetCurrentDebugLocation(cx.builder.B, metadata_node);
    }

    dbg_cx(cx).curr_loc = debug_location;
}

//=-------------------------------------------------------------------------------------------------
//  Utility Functions
//=-------------------------------------------------------------------------------------------------

#[inline]
fn roundup(x: uint, a: uint) -> uint {
    ((x + (a - 1)) / a) * a
}

/// Return codemap::Loc corresponding to the beginning of the span
fn span_start(cx: &CrateContext, span: Span) -> codemap::Loc {
    cx.sess.codemap.lookup_char_pos(span.lo)
}

fn size_and_align_of(cx: &mut CrateContext, llvm_type: Type) -> (uint, uint) {
    (machine::llsize_of_alloc(cx, llvm_type), machine::llalign_of_min(cx, llvm_type))
}

fn bytes_to_bits(bytes: uint) -> c_ulonglong {
    (bytes * 8) as c_ulonglong
}

#[inline]
fn dbg_cx<'a>(cx: &'a mut CrateContext) -> &'a mut CrateDebugContext {
    cx.dbg_cx.get_mut_ref()
}

#[inline]
fn DIB(cx: &CrateContext) -> DIBuilderRef {
    cx.dbg_cx.get_ref().builder
}

fn assert_fcx_has_span(fcx: &FunctionContext) {
    if fcx.span.is_none() {
        fcx.ccx.sess.bug(fmt!("debuginfo: Encountered function %s with invalid source span. \
            This function should have been ignored by debuginfo generation.",
            ast_map::path_to_str(fcx.path, fcx.ccx.sess.intr())));
    }
}

fn fn_should_be_ignored(fcx: &FunctionContext) -> bool {
    match fcx.debug_context {
        FunctionDebugContext(_) => false,
        _ => true
    }
}

// This procedure builds the *scope map* for a given function, which maps any given ast::NodeId in
// the function's AST to the correct DIScope metadata instance.
//
// This builder procedure walks the AST in execution order and keeps track of what belongs to which
// scope, creating DIScope DIEs along the way, and introducing *artificial* lexical scope
// descriptors where necessary. These artificial scopes allow GDB to correctly handle name
// shadowing.
fn populate_scope_map(cx: &mut CrateContext,
                      arg_pats: &[@ast::Pat],
                      fn_entry_block: Option<&ast::Block>,
                      fn_metadata: DISubprogram,
                      scope_map: &mut HashMap<ast::NodeId, DIScope>) {
    let def_map = cx.tcx.def_map;

    struct ScopeStackEntry {
        scope_metadata: DIScope,
        ident: Option<ast::Ident>
    }

    let mut scope_stack = ~[ScopeStackEntry { scope_metadata: fn_metadata, ident: None }];

    // Push argument identifiers onto the stack so arguments integrate nicely with variable
    // shadowing.
    for &arg_pat in arg_pats.iter() {
        do pat_util::pat_bindings(def_map, arg_pat) |_, _, _, path_ref| {
            let ident = ast_util::path_to_ident(path_ref);
            scope_stack.push(ScopeStackEntry { scope_metadata: fn_metadata, ident: Some(ident) });
        }
    }

    for &fn_entry_block in fn_entry_block.iter() {
        walk_block(cx, fn_entry_block, &mut scope_stack, scope_map);
    }


    // local helper functions for walking the AST.

    fn with_new_scope(cx: &mut CrateContext,
                      scope_span: Span,
                      scope_stack: &mut ~[ScopeStackEntry],
                      scope_map: &mut HashMap<ast::NodeId, DIScope>,
                      inner_walk: &fn(&mut CrateContext,
                                      &mut ~[ScopeStackEntry],
                                      &mut HashMap<ast::NodeId, DIScope>)) {
        // Create a new lexical scope and push it onto the stack
        let loc = cx.sess.codemap.lookup_char_pos(scope_span.lo);
        let file_metadata = file_metadata(cx, loc.file.name);
        let parent_scope = scope_stack.last().scope_metadata;

        let scope_metadata = unsafe {
            llvm::LLVMDIBuilderCreateLexicalBlock(
                DIB(cx),
                parent_scope,
                file_metadata,
                loc.line as c_uint,
                loc.col.to_uint() as c_uint)
        };

        scope_stack.push(ScopeStackEntry { scope_metadata: scope_metadata, ident: None });

        inner_walk(cx, scope_stack, scope_map);

        // pop artificial scopes
        while scope_stack.last().ident.is_some() {
            scope_stack.pop();
        }

        if scope_stack.last().scope_metadata != scope_metadata {
            cx.sess.span_bug(scope_span, "debuginfo: Inconsistency in scope management.");
        }

        scope_stack.pop();
    }

    fn walk_block(cx: &mut CrateContext,
                  block: &ast::Block,
                  scope_stack: &mut ~[ScopeStackEntry],
                  scope_map: &mut HashMap<ast::NodeId, DIScope>) {
        scope_map.insert(block.id, scope_stack.last().scope_metadata);

        // The interesting things here are statements and the concluding expression.
        for &@ ref statement in block.stmts.iter() {
            scope_map.insert(ast_util::stmt_id(statement), scope_stack.last().scope_metadata);

            match statement.node {
                ast::StmtDecl(@ref decl, _) => walk_decl(cx, decl, scope_stack, scope_map),
                ast::StmtExpr(@ref exp, _) |
                ast::StmtSemi(@ref exp, _) => walk_expr(cx, exp, scope_stack, scope_map),
                ast::StmtMac(*) => () // ignore macros (which should be expanded anyway)
            }
        }

        for &@ref exp in block.expr.iter() {
            walk_expr(cx, exp, scope_stack, scope_map);
        }
    }

    fn walk_decl(cx: &mut CrateContext,
                 decl: &ast::Decl,
                 scope_stack: &mut ~[ScopeStackEntry],
                 scope_map: &mut HashMap<ast::NodeId, DIScope>) {
        match *decl {
            codemap::Spanned { node: ast::DeclLocal(@ref local), _ } => {
                scope_map.insert(local.id, scope_stack.last().scope_metadata);

                walk_pattern(cx, local.pat, scope_stack, scope_map);

                for &@ref exp in local.init.iter() {
                    walk_expr(cx, exp, scope_stack, scope_map);
                }
            }
            _ => ()
        }
    }

    fn walk_pattern(cx: &mut CrateContext,
                    pat: @ast::Pat,
                    scope_stack: &mut ~[ScopeStackEntry],
                    scope_map: &mut HashMap<ast::NodeId, DIScope>) {

        let def_map = cx.tcx.def_map;

        // Unfortunately, we cannot just use pat_util::pat_bindings() or ast_util::walk_pat() here
        // because we have to visit *all* nodes in order to put them into the scope map. The above
        // functions don't do that.
        match pat.node {
            ast::PatIdent(_, ref path_ref, ref sub_pat_opt) => {

                // Check if this is a binding. If so we need to put it on the scope stack and maybe
                // introduce an articial scope
                if pat_util::pat_is_binding(def_map, pat) {

                    let ident = ast_util::path_to_ident(path_ref);

                    // LLVM does not properly generate 'DW_AT_start_scope' fields for variable DIEs.
                    // For this reason we have to introduce an artificial scope at bindings whenever
                    // a variable with the same name is declared in *any* parent scope.
                    //
                    // Otherwise the following error occurs:
                    //
                    // let x = 10;
                    //
                    // do_something(); // 'gdb print x' correctly prints 10
                    //
                    // {
                    //     do_something(); // 'gdb print x' prints 0, because it already reads the
                    //                     // uninitialized 'x' from the next line...
                    //     let x = 100;
                    //     do_something(); // 'gdb print x' correctly prints 100
                    // }

                    // Is there already a binding with that name?
                    // N.B.: this comparison must be UNhygienic... because
                    // gdb knows nothing about the context, so any two
                    // variables with the same name will cause the problem.
                    let need_new_scope = scope_stack
                        .iter()
                        .any(|entry| entry.ident.iter().any(|i| i.name == ident.name));

                    if need_new_scope {
                        // Create a new lexical scope and push it onto the stack
                        let loc = cx.sess.codemap.lookup_char_pos(pat.span.lo);
                        let file_metadata = file_metadata(cx, loc.file.name);
                        let parent_scope = scope_stack.last().scope_metadata;

                        let scope_metadata = unsafe {
                            llvm::LLVMDIBuilderCreateLexicalBlock(
                                DIB(cx),
                                parent_scope,
                                file_metadata,
                                loc.line as c_uint,
                                loc.col.to_uint() as c_uint)
                        };

                        scope_stack.push(ScopeStackEntry {
                            scope_metadata: scope_metadata,
                            ident: Some(ident)
                        });

                    } else {
                        // Push a new entry anyway so the name can be found
                        let prev_metadata = scope_stack.last().scope_metadata;
                        scope_stack.push(ScopeStackEntry {
                            scope_metadata: prev_metadata,
                            ident: Some(ident)
                        });
                    }
                }

                scope_map.insert(pat.id, scope_stack.last().scope_metadata);

                for &sub_pat in sub_pat_opt.iter() {
                    walk_pattern(cx, sub_pat, scope_stack, scope_map);
                }
            }

            ast::PatWild => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);
            }

            ast::PatEnum(_, ref sub_pats_opt) => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);

                for ref sub_pats in sub_pats_opt.iter() {
                    for &p in sub_pats.iter() {
                        walk_pattern(cx, p, scope_stack, scope_map);
                    }
                }
            }

            ast::PatStruct(_, ref field_pats, _) => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);

                for &ast::FieldPat { pat: sub_pat, _ } in field_pats.iter() {
                    walk_pattern(cx, sub_pat, scope_stack, scope_map);
                }
            }

            ast::PatTup(ref sub_pats) => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);

                for &sub_pat in sub_pats.iter() {
                    walk_pattern(cx, sub_pat, scope_stack, scope_map);
                }
            }

            ast::PatBox(sub_pat)    |
            ast::PatUniq(sub_pat)   |
            ast::PatRegion(sub_pat) => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);
                walk_pattern(cx, sub_pat, scope_stack, scope_map);
            }

            ast::PatLit(@ref exp) => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);
                walk_expr(cx, exp, scope_stack, scope_map);
            }

            ast::PatRange(@ref exp1, @ref exp2) => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);
                walk_expr(cx, exp1, scope_stack, scope_map);
                walk_expr(cx, exp2, scope_stack, scope_map);
            }

            ast::PatVec(ref front_sub_pats, ref middle_sub_pats, ref back_sub_pats) => {
                scope_map.insert(pat.id, scope_stack.last().scope_metadata);

                for &sub_pat in front_sub_pats.iter() {
                    walk_pattern(cx, sub_pat, scope_stack, scope_map);
                }

                for &sub_pat in middle_sub_pats.iter() {
                    walk_pattern(cx, sub_pat, scope_stack, scope_map);
                }

                for &sub_pat in back_sub_pats.iter() {
                    walk_pattern(cx, sub_pat, scope_stack, scope_map);
                }
            }
        }
    }

    fn walk_expr(cx: &mut CrateContext,
                 exp: &ast::Expr,
                 scope_stack: &mut ~[ScopeStackEntry],
                 scope_map: &mut HashMap<ast::NodeId, DIScope>) {

        scope_map.insert(exp.id, scope_stack.last().scope_metadata);

        match exp.node {
            ast::ExprSelf     |
            ast::ExprLit(_)   |
            ast::ExprBreak(_) |
            ast::ExprAgain(_) |
            ast::ExprPath(_)  => (),

            ast::ExprVstore(@ref sub_exp, _)   |
            ast::ExprCast(@ref sub_exp, _)     |
            ast::ExprAddrOf(_, @ref sub_exp)  |
            ast::ExprField(@ref sub_exp, _, _) |
            ast::ExprParen(@ref sub_exp)       => walk_expr(cx, sub_exp, scope_stack, scope_map),

            ast::ExprRet(exp_opt) => match exp_opt {
                Some(@ref sub_exp) => walk_expr(cx, sub_exp, scope_stack, scope_map),
                None => ()
            },

            ast::ExprUnary(node_id, _, @ref sub_exp) => {
                scope_map.insert(node_id, scope_stack.last().scope_metadata);
                walk_expr(cx, sub_exp, scope_stack, scope_map);
            }

            ast::ExprAssignOp(node_id, _, @ref lhs, @ref rhs) |
            ast::ExprIndex(node_id, @ref lhs, @ref rhs)        |
            ast::ExprBinary(node_id, _, @ref lhs, @ref rhs)    => {
                scope_map.insert(node_id, scope_stack.last().scope_metadata);
                walk_expr(cx, lhs, scope_stack, scope_map);
                walk_expr(cx, rhs, scope_stack, scope_map);
            }

            ast::ExprVec(ref init_expressions, _) |
            ast::ExprTup(ref init_expressions)    => {
                for &@ref ie in init_expressions.iter() {
                    walk_expr(cx, ie, scope_stack, scope_map);
                }
            }

            ast::ExprAssign(@ref sub_exp1, @ref sub_exp2)    |
            ast::ExprLog(@ref sub_exp1, @ref sub_exp2)       |
            ast::ExprRepeat(@ref sub_exp1, @ref sub_exp2, _) => {
                walk_expr(cx, sub_exp1, scope_stack, scope_map);
                walk_expr(cx, sub_exp2, scope_stack, scope_map);
            }

            ast::ExprIf(@ref cond_exp, ref then_block, ref opt_else_exp) => {
                walk_expr(cx, cond_exp, scope_stack, scope_map);

                do with_new_scope(cx, then_block.span, scope_stack, scope_map) |cx,
                                                                                scope_stack,
                                                                                scope_map| {
                    walk_block(cx, then_block, scope_stack, scope_map);
                }

                match *opt_else_exp {
                    Some(@ref else_exp) => walk_expr(cx, else_exp, scope_stack, scope_map),
                    _ => ()
                }
            }

            ast::ExprWhile(@ref cond_exp, ref loop_body) => {
                walk_expr(cx, cond_exp, scope_stack, scope_map);

                do with_new_scope(cx, loop_body.span, scope_stack, scope_map) |cx,
                                                                               scope_stack,
                                                                               scope_map| {
                    walk_block(cx, loop_body, scope_stack, scope_map);
                }
            }

            ast::ExprForLoop(_, _, _, _) => {
                cx.sess.span_bug(exp.span, "debuginfo::populate_scope_map() - \
                                            Found unexpanded for-loop.");
            }

            ast::ExprMac(_) => {
                cx.sess.span_bug(exp.span, "debuginfo::populate_scope_map() - \
                                            Found unexpanded macro.");
            }

            ast::ExprLoop(ref block, _) |
            ast::ExprBlock(ref block)   => {
                do with_new_scope(cx, block.span, scope_stack, scope_map) |cx,
                                                                           scope_stack,
                                                                           scope_map| {
                    walk_block(cx, block, scope_stack, scope_map);
                }
            }

            ast::ExprFnBlock(ast::fn_decl { inputs: ref inputs, _ }, ref block) => {
                do with_new_scope(cx, block.span, scope_stack, scope_map) |cx,
                                                                           scope_stack,
                                                                           scope_map| {
                    for &ast::arg { pat: pattern, _ } in inputs.iter() {
                        walk_pattern(cx, pattern, scope_stack, scope_map);
                    }

                    walk_block(cx, block, scope_stack, scope_map);
                }
            }

            // ast::expr_loop_body(@ref inner_exp) |
            ast::ExprDoBody(@ref inner_exp)   => {
                let inner_expr_is_expr_fn_block = match *inner_exp {
                    ast::Expr { node: ast::ExprFnBlock(*), _ } => true,
                    _ => false
                };

                if !inner_expr_is_expr_fn_block {
                    cx.sess.span_bug(inner_exp.span, "debuginfo: Inner expression was expected \
                                                      to be an ast::expr_fn_block.");
                }

                walk_expr(cx, inner_exp, scope_stack, scope_map);
            }

            ast::ExprCall(@ref fn_exp, ref args, _) => {
                walk_expr(cx, fn_exp, scope_stack, scope_map);

                for &@ref arg_exp in args.iter() {
                    walk_expr(cx, arg_exp, scope_stack, scope_map);
                }
            }

            ast::ExprMethodCall(node_id, @ref receiver_exp, _, _, ref args, _) => {
                scope_map.insert(node_id, scope_stack.last().scope_metadata);
                walk_expr(cx, receiver_exp, scope_stack, scope_map);

                for &@ref arg_exp in args.iter() {
                    walk_expr(cx, arg_exp, scope_stack, scope_map);
                }
            }

            ast::ExprMatch(@ref discriminant_exp, ref arms) => {
                walk_expr(cx, discriminant_exp, scope_stack, scope_map);

                // for each arm we have to first walk the pattern as these might introduce new
                // artificial scopes. It should be sufficient to walk only one pattern per arm, as
                // they all must contain the same binding names

                for arm_ref in arms.iter() {
                    let arm_span = arm_ref.pats[0].span;

                    do with_new_scope(cx, arm_span, scope_stack, scope_map) |cx,
                                                                             scope_stack,
                                                                             scope_map| {
                        for &pat in arm_ref.pats.iter() {
                            walk_pattern(cx, pat, scope_stack, scope_map);
                        }

                        for &@ref guard_exp in arm_ref.guard.iter() {
                            walk_expr(cx, guard_exp, scope_stack, scope_map)
                        }

                        walk_block(cx, &arm_ref.body, scope_stack, scope_map);
                    }
                }
            }

            ast::ExprStruct(_, ref fields, ref base_exp) => {
                for &ast::Field { expr: @ref exp, _ } in fields.iter() {
                    walk_expr(cx, exp, scope_stack, scope_map);
                }

                match *base_exp {
                    Some(@ref exp) => walk_expr(cx, exp, scope_stack, scope_map),
                    None => ()
                }
            }

            ast::ExprInlineAsm(ast::inline_asm { inputs: ref inputs,
                                                   outputs: ref outputs,
                                                   _ }) => {
                // inputs, outputs: ~[(@str, @expr)]
                for &(_, @ref exp) in inputs.iter() {
                    walk_expr(cx, exp, scope_stack, scope_map);
                }

                for &(_, @ref exp) in outputs.iter() {
                    walk_expr(cx, exp, scope_stack, scope_map);
                }
            }
        }
    }
}
