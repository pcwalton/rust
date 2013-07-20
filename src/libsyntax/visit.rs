// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use abi::AbiSet;
use ast::*;
use ast;
use codemap::span;
use parse;
use opt_vec;
use opt_vec::OptVec;

// Context-passing AST walker. Each overridden visit method has full control
// over what happens with its node, it can do its own traversal of the node's
// children (potentially passing in different contexts to each), call
// visit::visit_* to apply the default traversal algorithm (again, it can
// override the context), or prevent deeper traversal by doing nothing.
//
// Note: it is an important invariant that the default visitor walks the body
// of a function in "execution order" (more concretely, reverse post-order
// with respect to the CFG implied by the AST), meaning that if AST node A may
// execute before AST node B, then A is visited first.  The borrow checker in
// particular relies on this property.

pub enum fn_kind<'self> {
    // fn foo() or extern "Abi" fn foo()
    fk_item_fn(ident, &'self Generics, purity, AbiSet),

    // fn foo(&self)
    fk_method(ident, &'self Generics, &'self method),

    // @fn(x, y) { ... }
    fk_anon(ast::Sigil),

    // |x, y| ...
    fk_fn_block,
}

pub fn name_of_fn(fk: &fn_kind) -> ident {
    match *fk {
      fk_item_fn(name, _, _, _) | fk_method(name, _, _) => {
          name
      }
      fk_anon(*) | fk_fn_block(*) => parse::token::special_idents::anon,
    }
}

pub fn generics_of_fn(fk: &fn_kind) -> Generics {
    match *fk {
        fk_item_fn(_, generics, _, _) |
        fk_method(_, generics, _) => {
            (*generics).clone()
        }
        fk_anon(*) | fk_fn_block(*) => {
            Generics {
                lifetimes: opt_vec::Empty,
                ty_params: opt_vec::Empty,
            }
        }
    }
}

pub trait Visitor<E> {
    fn visit_mod(@mut self, &_mod, span, node_id, E);
    fn visit_view_item(@mut self, &view_item, E);
    fn visit_foreign_item(@mut self, @foreign_item, E);
    fn visit_item(@mut self, @item, E);
    fn visit_local(@mut self, @local, E);
    fn visit_block(@mut self, &blk, E);
    fn visit_stmt(@mut self, @stmt, E);
    fn visit_arm(@mut self, &arm, E);
    fn visit_pat(@mut self, @pat, E);
    fn visit_decl(@mut self, @decl, E);
    fn visit_expr(@mut self, @expr, E);
    fn visit_expr_post(@mut self, @expr, E);
    fn visit_ty(@mut self, &Ty, E);
    fn visit_generics(@mut self, &Generics, E);
    fn visit_fn(@mut self, &fn_kind, &fn_decl, &blk, span, node_id, E);
    fn visit_ty_method(@mut self, &ty_method, E);
    fn visit_trait_method(@mut self, &trait_method, E);
    fn visit_struct_def(@mut self, @struct_def, ident, &Generics, node_id, E);
    fn visit_struct_field(@mut self, @struct_field, E);
}

pub fn visit_crate<E:Clone>(visitor: @Visitor<E>, crate: &crate, env: E) {
    visitor.visit_mod(&crate.node.module, crate.span, crate_node_id, env)
}

pub fn visit_mod<E:Clone>(visitor: @Visitor<E>, module: &_mod, env: E) {
    for module.view_items.iter().advance |view_item| {
        visitor.visit_view_item(view_item, env.clone())
    }
    for module.items.iter().advance |item| {
        visitor.visit_item(*item, env.clone())
    }
}

pub fn visit_view_item<E:Clone>(visitor: @Visitor<E>,
                                view_item: &view_item,
                                _: E) {
    // Empty!
}

pub fn visit_local<E:Clone>(visitor: @Visitor<E>, local: &local, env: E) {
    visitor.visit_pat(local.node.pat, env.clone());
    visitor.visit_ty(&local.node.ty, env.clone());
    match local.node.init {
        None => {}
        Some(initializer) => visitor.visit_expr(initializer, env),
    }
}

fn visit_trait_ref<E:Clone>(visitor: @Visitor<E>,
                            trait_ref: &ast::trait_ref,
                            env: E) {
    visit_path(visitor, &trait_ref.path, env)
}

pub fn visit_item<E:Clone>(visitor: @Visitor<E>, item: &item, env: E) {
    match item.node {
        item_static(ref typ, _, expr) => {
            visitor.visit_ty(typ, env.clone());
            visitor.visit_expr(expr, env);
        }
        item_fn(ref declaration, purity, abi, ref generics, ref body) => {
            visitor.visit_fn(&fk_item_fn(item.ident, generics, purity, abi),
                             declaration,
                             body,
                             item.span,
                             item.id,
                             env)
        }
        item_mod(ref module) => {
            visitor.visit_mod(module, item.span, item.id, env)
        }
        item_foreign_mod(ref foreign_module) => {
            for foreign_module.view_items.iter().advance |view_item| {
                visitor.visit_view_item(view_item, env.clone())
            }
            for foreign_module.items.iter().advance |foreign_item| {
                visitor.visit_foreign_item(*foreign_item, env.clone())
            }
        }
        item_ty(ref typ, ref type_parameters) => {
            visitor.visit_ty(typ, env.clone());
            visitor.visit_generics(type_parameters, env)
        }
        item_enum(ref enum_definition, ref type_parameters) => {
            visitor.visit_generics(type_parameters, env.clone());
            visit_enum_def(visitor, enum_definition, type_parameters, env)
        }
        item_impl(ref type_parameters,
                  ref trait_references,
                  ref typ,
                  ref methods) => {
            visitor.visit_generics(type_parameters, env.clone());
            for trait_references.iter().advance |trait_reference| {
                visit_trait_ref(visitor, trait_reference, env.clone())
            }
            visitor.visit_ty(typ, env.clone());
            for methods.iter().advance |method| {
                visit_method_helper(visitor, *method, env.clone())
            }
        }
        item_struct(struct_definition, ref generics) => {
            visitor.visit_generics(generics, env.clone());
            visitor.visit_struct_def(struct_definition,
                                     item.ident,
                                     generics,
                                     item.id,
                                     env)
        }
        item_trait(ref generics, ref trait_paths, ref methods) => {
            visitor.visit_generics(generics, env.clone());
            for trait_paths.iter().advance |trait_path| {
                visit_path(visitor, &trait_path.path, env.clone())
            }
            for methods.iter().advance |method| {
                visitor.visit_trait_method(method, env.clone())
            }
        }
        item_mac(ref macro) => visit_mac(visitor, macro, env),
    }
}

pub fn visit_enum_def<E:Clone>(visitor: @Visitor<E>,
                               enum_definition: &ast::enum_def,
                               generics: &Generics,
                               env: E) {
    for enum_definition.variants.iter().advance |variant| {
        match variant.node.kind {
            tuple_variant_kind(ref variant_arguments) => {
                for variant_arguments.iter().advance |variant_argument| {
                    visitor.visit_ty(&variant_argument.ty, env.clone())
                }
            }
            struct_variant_kind(struct_definition) => {
                visitor.visit_struct_def(struct_definition,
                                         variant.node.name,
                                         generics,
                                         variant.node.id,
                                         env.clone())
            }
        }
    }
}

pub fn skip_ty<E>(_: @Visitor<E>, _: &Ty, _: E) {
    // Empty!
}

pub fn visit_ty<E:Clone>(visitor: @Visitor<E>, typ: &Ty, env: E) {
    match typ.node {
        ty_box(ref mutable_type) | ty_uniq(ref mutable_type) |
        ty_vec(ref mutable_type) | ty_ptr(ref mutable_type) |
        ty_rptr(_, ref mutable_type) => {
            visitor.visit_ty(mutable_type.ty, env)
        }
        ty_tup(ref tuple_element_types) => {
            for tuple_element_types.iter().advance |tuple_element_type| {
                visitor.visit_ty(tuple_element_type, env.clone())
            }
        }
        ty_closure(ref function_declaration) => {
             for function_declaration.decl.inputs.iter().advance |argument| {
                visitor.visit_ty(&argument.ty, env.clone())
             }
             visitor.visit_ty(&function_declaration.decl.output, env.clone());
             for function_declaration.bounds.iter().advance |bounds| {
                visit_ty_param_bounds(visitor, bounds, env.clone())
             }
        }
        ty_bare_fn(ref function_declaration) => {
            for function_declaration.decl.inputs.iter().advance |argument| {
                visitor.visit_ty(&argument.ty, env.clone())
            }
            visitor.visit_ty(&function_declaration.decl.output, env.clone())
        }
        ty_path(ref path, ref bounds, _) => {
            visit_path(visitor, path, env.clone());
            for bounds.iter().advance |bounds| {
                visit_ty_param_bounds(visitor, bounds, env.clone())
            }
        }
        ty_fixed_length_vec(ref mutable_type, expression) => {
            visitor.visit_ty(mutable_type.ty, env.clone());
            visitor.visit_expr(expression, env)
        }
        ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
    }
}

pub fn visit_path<E:Clone>(visitor: @Visitor<E>, path: &Path, env: E) {
    for path.types.iter().advance |typ| {
        visitor.visit_ty(typ, env.clone())
    }
}

pub fn visit_pat<E:Clone>(visitor: @Visitor<E>, pattern: &pat, env: E) {
    match pattern.node {
        pat_enum(ref path, ref children) => {
            visit_path(visitor, path, env.clone());
            for children.iter().advance |children| {
                for children.iter().advance |child| {
                    visitor.visit_pat(*child, env.clone())
                }
            }
        }
        pat_struct(ref path, ref fields, _) => {
            visit_path(visitor, path, env.clone());
            for fields.iter().advance |field| {
                visitor.visit_pat(field.pat, env.clone())
            }
        }
        pat_tup(ref tuple_elements) => {
            for tuple_elements.iter().advance |tuple_element| {
                visitor.visit_pat(*tuple_element, env.clone())
            }
        }
        pat_box(subpattern) |
        pat_uniq(subpattern) |
        pat_region(subpattern) => {
            visitor.visit_pat(subpattern, env)
        }
        pat_ident(_, ref path, ref optional_subpattern) => {
            visit_path(visitor, path, env.clone());
            match *optional_subpattern {
                None => {}
                Some(subpattern) => visitor.visit_pat(subpattern, env),
            }
        }
        pat_lit(expression) => visitor.visit_expr(expression, env),
        pat_range(lower_bound, upper_bound) => {
            visitor.visit_expr(lower_bound, env.clone());
            visitor.visit_expr(upper_bound, env)
        }
        pat_wild => (),
        pat_vec(ref prepattern, ref slice_pattern, ref postpatterns) => {
            for prepattern.iter().advance |prepattern| {
                visitor.visit_pat(*prepattern, env.clone())
            }
            for slice_pattern.iter().advance |slice_pattern| {
                visitor.visit_pat(*slice_pattern, env.clone())
            }
            for postpatterns.iter().advance |postpattern| {
                visitor.visit_pat(*postpattern, env.clone())
            }
        }
    }
}

pub fn visit_foreign_item<E:Clone>(visitor: @Visitor<E>,
                                   foreign_item: &foreign_item,
                                   env: E) {
    match foreign_item.node {
        foreign_item_fn(ref function_declaration, _, ref generics) => {
            visit_fn_decl(visitor, function_declaration, env.clone());
            visitor.visit_generics(generics, env)
        }
        foreign_item_static(ref typ, _) => visitor.visit_ty(typ, env),
    }
}

pub fn visit_ty_param_bounds<E:Clone>(visitor: @Visitor<E>,
                                      bounds: &OptVec<TyParamBound>,
                                      env: E) {
    for bounds.iter().advance |bound| {
        match *bound {
            TraitTyParamBound(ref typ) => {
                visit_trait_ref(visitor, typ, env.clone())
            }
            RegionTyParamBound => {}
        }
    }
}

pub fn visit_generics<E:Clone>(visitor: @Visitor<E>,
                               generics: &Generics,
                               env: E) {
    for generics.ty_params.iter().advance |type_parameter| {
        visit_ty_param_bounds(visitor, &type_parameter.bounds, env.clone())
    }
}

pub fn visit_fn_decl<E:Clone>(visitor: @Visitor<E>,
                              function_declaration: &fn_decl,
                              env: E) {
    for function_declaration.inputs.iter().advance |argument| {
        visitor.visit_pat(argument.pat, env.clone());
        visitor.visit_ty(&argument.ty, env.clone())
    }
    visitor.visit_ty(&function_declaration.output, env)
}

// Note: there is no visit_method() method in the visitor, instead override
// visit_fn() and check for fk_method().  I named this visit_method_helper()
// because it is not a default impl of any method, though I doubt that really
// clarifies anything. - Niko
pub fn visit_method_helper<E:Clone>(visitor: @Visitor<E>,
                                    method: &method,
                                    env: E) {
    visitor.visit_fn(&fk_method(method.ident, &method.generics, method),
                     &method.decl,
                     &method.body,
                     method.span,
                     method.id,
                     env)
}

pub fn visit_fn<E:Clone>(visitor: @Visitor<E>,
                         function_kind: &fn_kind,
                         function_declaration: &fn_decl,
                         function_body: &blk,
                         _: span,
                         _: node_id,
                         env: E) {
    visit_fn_decl(visitor, function_declaration, env.clone());
    let generics = generics_of_fn(function_kind);
    visitor.visit_generics(&generics, env.clone());
    visitor.visit_block(function_body, env)
}

pub fn visit_ty_method<E:Clone>(visitor: @Visitor<E>,
                                method_type: &ty_method,
                                env: E) {
    for method_type.decl.inputs.iter().advance |argument_type| {
        visitor.visit_ty(&argument_type.ty, env.clone())
    }
    visitor.visit_generics(&method_type.generics, env.clone());
    visitor.visit_ty(&method_type.decl.output, env.clone())
}

pub fn visit_trait_method<E:Clone>(visitor: @Visitor<E>,
                                   trait_method: &trait_method,
                                   env: E) {
    match *trait_method {
        required(ref method_type) => {
            visitor.visit_ty_method(method_type, env)
        }
        provided(method) => visit_method_helper(visitor, method, env),
    }
}

pub fn visit_struct_def<E:Clone>(visitor: @Visitor<E>,
                                 struct_definition: @struct_def,
                                 _: ast::ident,
                                 _: &Generics,
                                 _: node_id,
                                 env: E) {
    for struct_definition.fields.iter().advance |field| {
        visitor.visit_struct_field(*field, env.clone())
    }
}

pub fn visit_struct_field<E:Clone>(visitor: @Visitor<E>,
                                   struct_field: &struct_field,
                                   env: E) {
    visitor.visit_ty(&struct_field.node.ty, env)
}

pub fn visit_block<E:Clone>(visitor: @Visitor<E>, block: &blk, env: E) {
    for block.view_items.iter().advance |view_item| {
        visitor.visit_view_item(view_item, env.clone())
    }
    for block.stmts.iter().advance |statement| {
        visitor.visit_stmt(*statement, env.clone())
    }
    visit_expr_opt(visitor, block.expr, env)
}

pub fn visit_stmt<E>(visitor: @Visitor<E>, statement: &stmt, env: E) {
    match statement.node {
        stmt_decl(declaration, _) => visitor.visit_decl(declaration, env),
        stmt_expr(expression, _) | stmt_semi(expression, _) => {
            visitor.visit_expr(expression, env)
        }
        stmt_mac(ref macro, _) => visit_mac(visitor, macro, env),
    }
}

pub fn visit_decl<E:Clone>(visitor: @Visitor<E>, declaration: &decl, env: E) {
    match declaration.node {
        decl_local(ref local) => visitor.visit_local(*local, env),
        decl_item(item) => visitor.visit_item(item, env),
    }
}

pub fn visit_expr_opt<E>(visitor: @Visitor<E>,
                         optional_expression: Option<@expr>,
                         env: E) {
    match optional_expression {
        None => {}
        Some(expression) => visitor.visit_expr(expression, env),
    }
}

pub fn visit_exprs<E:Clone>(visitor: @Visitor<E>,
                            expressions: &[@expr],
                            env: E) {
    for expressions.iter().advance |expression| {
        visitor.visit_expr(*expression, env.clone())
    }
}

pub fn visit_mac<E>(_: @Visitor<E>, _: &mac, _: E) {
    // Empty!
}

pub fn visit_expr<E:Clone>(visitor: @Visitor<E>, expression: @expr, env: E) {
    match expression.node {
        expr_vstore(subexpression, _) => {
            visitor.visit_expr(subexpression, env.clone())
        }
        expr_vec(ref subexpressions, _) => {
            visit_exprs(visitor, *subexpressions, env.clone())
        }
        expr_repeat(element, count, _) => {
            visitor.visit_expr(element, env.clone());
            visitor.visit_expr(count, env.clone())
        }
        expr_struct(ref path, ref fields, optional_base) => {
            visit_path(visitor, path, env.clone());
            for fields.iter().advance |field| {
                visitor.visit_expr(field.node.expr, env.clone())
            }
            visit_expr_opt(visitor, optional_base, env.clone())
        }
        expr_tup(ref subexpressions) => {
            for subexpressions.iter().advance |subexpression| {
                visitor.visit_expr(*subexpression, env.clone())
            }
        }
        expr_call(callee_expression, ref arguments, _) => {
            for arguments.iter().advance |argument| {
                visitor.visit_expr(*argument, env.clone())
            }
            visitor.visit_expr(callee_expression, env.clone())
        }
        expr_method_call(_, callee, _, ref types, ref arguments, _) => {
            visit_exprs(visitor, *arguments, env.clone());
            for types.iter().advance |typ| {
                visitor.visit_ty(typ, env.clone())
            }
            visitor.visit_expr(callee, env.clone())
        }
        expr_binary(_, _, left_expression, right_expression) => {
            visitor.visit_expr(left_expression, env.clone());
            visitor.visit_expr(right_expression, env.clone())
        }
        expr_addr_of(_, subexpression) |
        expr_unary(_, _, subexpression) |
        expr_loop_body(subexpression) |
        expr_do_body(subexpression) => {
            visitor.visit_expr(subexpression, env.clone())
        }
        expr_lit(_) => {}
        expr_cast(subexpression, ref typ) => {
            visitor.visit_expr(subexpression, env.clone());
            visitor.visit_ty(typ, env.clone())
        }
        expr_if(head_expression, ref if_block, optional_else) => {
            visitor.visit_expr(head_expression, env.clone());
            visitor.visit_block(if_block, env.clone());
            visit_expr_opt(visitor, optional_else, env.clone())
        }
        expr_while(subexpression, ref block) => {
            visitor.visit_expr(subexpression, env.clone());
            visitor.visit_block(block, env.clone())
        }
        expr_loop(ref block, _) => visitor.visit_block(block, env.clone()),
        expr_match(subexpression, ref arms) => {
            visitor.visit_expr(subexpression, env.clone());
            for arms.iter().advance |arm| {
                visitor.visit_arm(arm, env.clone())
            }
        }
        expr_fn_block(ref function_declaration, ref body) => {
            visitor.visit_fn(&fk_fn_block,
                             function_declaration,
                             body,
                             expression.span,
                             expression.id,
                             env.clone())
        }
        expr_block(ref block) => visitor.visit_block(block, env.clone()),
        expr_assign(left_hand_expression, right_hand_expression) => {
            visitor.visit_expr(right_hand_expression, env.clone());
            visitor.visit_expr(left_hand_expression, env.clone())
        }
        expr_assign_op(_, _, left_expression, right_expression) => {
            visitor.visit_expr(right_expression, env.clone());
            visitor.visit_expr(left_expression, env.clone())
        }
        expr_field(subexpression, _, ref types) => {
            visitor.visit_expr(subexpression, env.clone());
            for types.iter().advance |typ| {
                visitor.visit_ty(typ, env.clone())
            }
        }
        expr_index(_, main_expression, index_expression) => {
            visitor.visit_expr(main_expression, env.clone());
            visitor.visit_expr(index_expression, env.clone())
        }
        expr_path(ref path) => visit_path(visitor, path, env.clone()),
        expr_self | expr_break(_) | expr_again(_) => {}
        expr_ret(optional_expression) => {
            visit_expr_opt(visitor, optional_expression, env.clone())
        }
        expr_log(level, subexpression) => {
            visitor.visit_expr(level, env.clone());
            visitor.visit_expr(subexpression, env.clone());
        }
        expr_mac(ref macro) => visit_mac(visitor, macro, env.clone()),
        expr_paren(subexpression) => {
            visitor.visit_expr(subexpression, env.clone())
        }
        expr_inline_asm(ref assembler) => {
            for assembler.inputs.iter().advance |&(_, input)| {
                visitor.visit_expr(input, env.clone())
            }
            for assembler.outputs.iter().advance |&(_, output)| {
                visitor.visit_expr(output, env.clone())
            }
        }
    }

    visitor.visit_expr_post(expression, env.clone())
}

pub fn visit_arm<E:Clone>(visitor: @Visitor<E>, arm: &arm, env: E) {
    for arm.pats.iter().advance |pattern| {
        visitor.visit_pat(*pattern, env.clone())
    }
    visit_expr_opt(visitor, arm.guard, env.clone());
    visitor.visit_block(&arm.body, env)
}

// Simpler, non-context passing interface. Always walks the whole tree, simply
// calls the given functions on the nodes.

pub trait SimpleVisitor {
    fn visit_mod(&_mod, span, node_id);
    fn visit_view_item(&view_item);
    fn visit_foreign_item(@foreign_item);
    fn visit_item(@item);
    fn visit_local(@local);
    fn visit_block(&blk);
    fn visit_stmt(@stmt);
    fn visit_arm(&arm);
    fn visit_pat(@pat);
    fn visit_decl(@decl);
    fn visit_expr(@expr);
    fn visit_expr_post(@expr);
    fn visit_ty(&Ty);
    fn visit_generics(&Generics);
    fn visit_fn(&fn_kind, &fn_decl, &blk, span, node_id);
    fn visit_ty_method(&ty_method);
    fn visit_trait_method(&trait_method);
    fn visit_struct_def(@struct_def, ident, &Generics, node_id);
    fn visit_struct_field(@struct_field);
    fn visit_struct_method(@method);
}

/*pub fn simple_ignore_ty(_t: &Ty) {}

pub fn default_simple_visitor() -> @SimpleVisitor {
    @SimpleVisitor {
        visit_mod: |_m, _sp, _id| { },
        visit_view_item: |_vi| { },
        visit_foreign_item: |_ni| { },
        visit_item: |_i| { },
        visit_local: |_l| { },
        visit_block: |_b| { },
        visit_stmt: |_s| { },
        visit_arm: |_a| { },
        visit_pat: |_p| { },
        visit_decl: |_d| { },
        visit_expr: |_e| { },
        visit_expr_post: |_e| { },
        visit_ty: simple_ignore_ty,
        visit_generics: |_| {},
        visit_fn: |_, _, _, _, _| {},
        visit_ty_method: |_| {},
        visit_trait_method: |_| {},
        visit_struct_def: |_, _, _, _| {},
        visit_struct_field: |_| {},
        visit_struct_method: |_| {},
    }
}

struct SimpleVisitorVisitor {
    simple_visitor: @SimpleVisitor,
}

impl Visitor for SimpleVisitorVisitor {
    fn visit_mod(module: &_mod, span: span, node_id, 
}

pub fn mk_simple_visitor(v: @SimpleVisitor) -> vt<()> {
    fn v_mod(f: @fn(&_mod, span, node_id),
             m: &_mod,
             sp: span,
             id: node_id,
             (e, v): ((), vt<()>)) {
        f(m, sp, id);
        visit_mod(m, sp, id, (e, v));
    }
    fn v_view_item(f: @fn(&view_item), vi: &view_item, (e, v): ((), vt<()>)) {
        f(vi);
        visit_view_item(vi, (e, v));
    }
    fn v_foreign_item(f: @fn(@foreign_item), ni: @foreign_item, (e, v): ((), vt<()>)) {
        f(ni);
        visit_foreign_item(ni, (e, v));
    }
    fn v_item(f: @fn(@item), i: @item, (e, v): ((), vt<()>)) {
        f(i);
        visit_item(i, (e, v));
    }
    fn v_local(f: @fn(@local), l: @local, (e, v): ((), vt<()>)) {
        f(l);
        visit_local(l, (e, v));
    }
    fn v_block(f: @fn(&ast::blk), bl: &ast::blk, (e, v): ((), vt<()>)) {
        f(bl);
        visit_block(bl, (e, v));
    }
    fn v_stmt(f: @fn(@stmt), st: @stmt, (e, v): ((), vt<()>)) {
        f(st);
        visit_stmt(st, (e, v));
    }
    fn v_arm(f: @fn(&arm), a: &arm, (e, v): ((), vt<()>)) {
        f(a);
        visit_arm(a, (e, v));
    }
    fn v_pat(f: @fn(@pat), p: @pat, (e, v): ((), vt<()>)) {
        f(p);
        visit_pat(p, (e, v));
    }
    fn v_decl(f: @fn(@decl), d: @decl, (e, v): ((), vt<()>)) {
        f(d);
        visit_decl(d, (e, v));
    }
    fn v_expr(f: @fn(@expr), ex: @expr, (e, v): ((), vt<()>)) {
        f(ex);
        visit_expr(ex, (e, v));
    }
    fn v_expr_post(f: @fn(@expr), ex: @expr, (_e, _v): ((), vt<()>)) {
        f(ex);
    }
    fn v_ty(f: @fn(&Ty), ty: &Ty, (e, v): ((), vt<()>)) {
        f(ty);
        visit_ty(ty, (e, v));
    }
    fn v_ty_method(f: @fn(&ty_method), ty: &ty_method, (e, v): ((), vt<()>)) {
        f(ty);
        visit_ty_method(ty, (e, v));
    }
    fn v_trait_method(f: @fn(&trait_method),
                      m: &trait_method,
                      (e, v): ((), vt<()>)) {
        f(m);
        visit_trait_method(m, (e, v));
    }
    fn v_struct_def(
        f: @fn(@struct_def, ident, &Generics, node_id),
        sd: @struct_def,
        nm: ident,
        generics: &Generics,
        id: node_id,
        (e, v): ((), vt<()>)
    ) {
        f(sd, nm, generics, id);
        visit_struct_def(sd, nm, generics, id, (e, v));
    }
    fn v_generics(
        f: @fn(&Generics),
        ps: &Generics,
        (e, v): ((), vt<()>)
    ) {
        f(ps);
        visit_generics(ps, (e, v));
    }
    fn v_fn(
        f: @fn(&fn_kind, &fn_decl, &blk, span, node_id),
        fk: &fn_kind,
        decl: &fn_decl,
        body: &blk,
        sp: span,
        id: node_id,
        (e, v): ((), vt<()>)
    ) {
        f(fk, decl, body, sp, id);
        visit_fn(fk, decl, body, sp, id, (e, v));
    }
    let visit_ty: @fn(&Ty, ((), vt<()>)) =
        |a,b| v_ty(v.visit_ty, a, b);
    fn v_struct_field(f: @fn(@struct_field), sf: @struct_field, (e, v): ((), vt<()>)) {
        f(sf);
        visit_struct_field(sf, (e, v));
    }
    return mk_vt(@Visitor {
        visit_mod: |a,b,c,d|v_mod(v.visit_mod, a, b, c, d),
        visit_view_item: |a,b| v_view_item(v.visit_view_item, a, b),
        visit_foreign_item:
            |a,b|v_foreign_item(v.visit_foreign_item, a, b),
        visit_item: |a,b|v_item(v.visit_item, a, b),
        visit_local: |a,b|v_local(v.visit_local, a, b),
        visit_block: |a,b|v_block(v.visit_block, a, b),
        visit_stmt: |a,b|v_stmt(v.visit_stmt, a, b),
        visit_arm: |a,b|v_arm(v.visit_arm, a, b),
        visit_pat: |a,b|v_pat(v.visit_pat, a, b),
        visit_decl: |a,b|v_decl(v.visit_decl, a, b),
        visit_expr: |a,b|v_expr(v.visit_expr, a, b),
        visit_expr_post: |a,b| v_expr_post(v.visit_expr_post, a, b),
        visit_ty: visit_ty,
        visit_generics: |a,b|
            v_generics(v.visit_generics, a, b),
        visit_fn: |a,b,c,d,e,f|
            v_fn(v.visit_fn, a, b, c, d, e, f),
        visit_ty_method: |a,b|
            v_ty_method(v.visit_ty_method, a, b),
        visit_trait_method: |a,b|
            v_trait_method(v.visit_trait_method, a, b),
        visit_struct_def: |a,b,c,d,e|
            v_struct_def(v.visit_struct_def, a, b, c, d, e),
        visit_struct_field: |a,b|
            v_struct_field(v.visit_struct_field, a, b),
    });
}*/
