// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Name resolution.

use core::prelude::*;

use syntax::ast::{anonymous, def_id, item_const, item_enum, item_fn};
use syntax::ast::{item_foreign_mod};
use syntax::ast::{item_mac, item_trait, item_ty, mod_, named, public};
use syntax::ast::{unnamed_field, view_item, view_item_export};
use syntax::ast::{view_item_import, view_item_use, view_path};
use syntax::ast_util::local_def;
use syntax::visit;

use core::cast::transmute;
use core::libc::c_void;
use core::send_map::linear::LinearMap;

//
// Various types
//

condition! {
    unresolved_err: span, def_id -> ();
}

condition! {
    duplicate_err: &mut Moduloid, def_id -> ();
}

/*pub type ResolveResult = {
    def_map: DefMap,
    exp_map2: ExportMap2,
    trait_map: TraitMap
};*/
pub type ResolveResult = ();

type ModuloidVisitor = &fn(@Moduloid, &[view_item]);

struct Item(def_id);

// Type name bindings are special: they can either be associated with a module
// or a type and one or more type implementations.
enum TypeBindings {
    ModuleBinding(Item),
    TypeBinding {
        typedef: Option<Item>,
        impls: Option<~[Item]>, // Option<> to avoid heap allocation.
    }
}

enum Namespace {
    TypeNs,
    ValueNs,
}

//
// A moduloid is something that contains items. Modules (both local and
// external), type implementations, traits, and blocks that contain items are
// all moduloids.
//

struct Moduloid {
    /// The def ID of this moduloid.
    def_id: def_id,
    /// Whether this moduloid is populated or not. Moduloids are populated
    /// lazily from the AST and/or external crates.
    populated: bool,
    /// Type members.
    type_ns: LinearMap<ident,TypeBindings>,
    /// Value members.
    value_ns: LinearMap<ident,Item>,
}

impl Moduloid {
    // Returns the moduloid for the given def ID, creating it if it doesn't
    // already exist.
    static fn get(resolver: &mut Resolver, def_id: def_id) -> @Moduloid {
        match resolver.moduloids.find(def_id) {
            None => {
                let new_moduloid = @Moduloid {
                    def_id: def_id,
                    populated: false,
                    type_ns: LinearMap(),
                    value_ns: LinearMap(),
                };
                resolver.moduloids.insert(new_moduloid);
                new_moduloid
            }
            Some(moduloid) => moduloid
        }
    }

    // Returns the moduloid for the crate root.
    static fn get_root(resolver: &mut Resolver) -> @Moduloid {
        Moduloid::get(resolver, { crate: 0, node: 0 })
    }

    // Looks up the given module or impl binding in this moduloid and returns
    // it if found. This will not match types.
    fn lookup_module_or_impl(&mut self,
                             resolver: &mut Resolver,
                             ident: ident)
                          -> Option<def_id> {
        if !self.populated {
            self.populate(resolver);
        }

        match self.type_ns.
        self.resolve();
    }

    // Internal function to populate a moduloid. Don't call this directly;
    // it will be called automatically when you use any of the `lookup_foo()`
    // methods.
    //
    // For moduloids within this crate only, this does *not* populate the
    // contents of `pub use` directives. These are eagerly precomputed in a
    // separate pass. The eagerness does not hurt performance in this case,
    // since we have to resolve all modules within this crate anyhow.
    priv fn populate(&mut self, resolver: &mut Resolver) {
        if self.def_id.crate == local_crate {
            self.populate_local();
        } else {
            // XXX: self.populate_external();
        }
        self.populated = true;
    }

    // Internal function to populate a moduloid with the contents of a local
    // module or impl.
    priv fn populate_local(&mut self, resolver: &mut Resolver) {
        let item;
        match resolver.ast_map.find(self.def_id.node) {
            node_item(the_item, _) => item = the_item,
            _ => resolver.session.bug(~"moduloid wasn't an item")
        }

        match item.node {
            item_mod(module) => {
                self.populate_local_module(resolver, module)
            }
            item_foreign_mod(foreign_mod) => {
                self.populate_foreign_module(resolver, foreign_mod);
            }
            item_trait(_, _, trait_methods) => {
                // XXX
            }
            item_impl(_, None, _, methods) => {
                // XXX
            }
            _ => resolver.session.bug(~"moduloid wasn't a known item type")
        }
    }

    // Internal function to add a name to the value namespace. Raises an error
    // if the name is already bound.
    priv fn register_value(&mut self, name: ident, def_id: def_id) {
        // Error out here if there is a duplicate name.
        if self.value_ns.contains_key(name) {
            duplicate_err::cond.raise(self, def_id);
        }

        self.value_ns.insert(name, Item(def_id));
    }

    // Internal function to attach a module name to the type namespace.
    // Raises an error if the name is already bound to a module or type.
    priv fn register_module(&mut self, name: ident, def_id: def_id) {
        // Error out here if this is a duplicate name.
        if self.type_ns.contains_key(name) {
            duplicate_err::cond.raise(self, def_id);
        }

        self.type_ns.insert(name, ModuleBinding(Item(def_id)));
    }

    // Internal function to attach a type name to the type namespace.
    // Raises an error if the name is already bound to a module or a type.
    priv fn register_type(&mut self, name: ident, def_id: def_id) {
        let mut bindings;
        match self.type_ns.pop(name) {
            None => {
                bindings = TypeBinding { typedef: Some(def_id), impls: None };
            }
            Some(the_bindings) => {
                bindings = the_bindings;
                match bindings {
                    ModuleBinding(_) |
                    TypeBinding { typedef: Some(_), impls: _ } => {
                        duplicate_err::cond.raise(self, def_id);
                    }
                    TypeBinding { typedef: ref mut typedef, impls: _ } => {
                        *typedef = Some(Item(def_id));
                    }
                }
            }
        }
        self.type_ns.insert(name, bindings);
    }

    // Internal function to attach a type implementation name to the type
    // namespace. Raises an error if the name is already bound to a module.
    priv fn register_impl(&mut self, name: ident, def_id: def_id) {
        let mut bindings;
        match self.type_ns.pop(name) {
            None => {
                bindings = TypeBinding {
                    typedef: None,
                    impls: Some(~[ Item(def_id) ])
                };
            }
            Some(the_bindings) => {
                bindings = the_bindings;
                match bindings {
                    ModuleBinding(_) => {
                        duplicate_err::cond.raise(self, def_id);
                    }
                    TypeBinding { typedef: _, impls: ref mut impls } => {
                        match impls {
                            None => {
                                *impls = Some(~[ Item(def_id) ]);
                            }
                            Some(ref mut impl_list) => {
                                impl_list.push(Item(def_id));
                            }
                        }
                    }
                }
            }
        }
        self.type_ns.insert(name, bindings);
    }

    // Populates a regular, crate-local module full of items. Add each item to
    // the proper namespace.
    //
    // Note that we do *not* take privacy into account here. This is handled
    // later, in the "privacy" stage.
    priv fn populate_local_module(&mut self,
                                  resolver: &mut Resolver,
                                  module: &mod_) {
        for module.items.each |item| {
            match item.node {
                // Modules create module bindings in the type namespace.
                item_mod(*) => {
                    self.register_module(item.ident, local_def(item.node));
                }

                // Types create type bindings in the type namespace.
                item_ty(*) => {
                    self.register_type(item.ident, local_def(item.node));
                }

                // Type implementations create an impl binding in the type
                // namespace.
                item_impl(_, None, _, _) => {
                    self.register_impl(item.ident, local_def(item.node));
                }

                // Traits create both a type binding and an impl binding in
                // the type namespace.
                item_trait(*) => {
                    // XXX: Could be slightly more efficient here and create
                    // the binding all in one go instead of doing two lookups.
                    // Probably doesn't matter.
                    self.register_type(item.ident, local_def(item.node));
                    self.register_impl(item.ident, local_def(item.node));
                }

                // Constants and functions create value bindings.
                item_const(*) | item_fn(*) => {
                    self.register_value(item.ident, local_def(item.node));
                }

                // Macros and trait implementations create no bindings.
                item_mac(*) | item_impl(*) => {}

                // Enums create a type binding in the type namespace and
                // value or type bindings for each of their variants.
                item_enum(ref enum_def, _) => {
                    self.register_type(item.ident, local_def(item.node));

                    for enum_def.variants.each |variant| {
                        let name = variant.node.name;
                        let variant_did = local_def(variant.node.id));
                        match variant.node.kind {
                            tuple_variant_kind |
                            enum_variant_kind => {
                                self.register_value(name, variant_did);
                            }
                            struct_variant_kind => {
                                self.register_type(name, variant_did);
                            }
                        }
                    }
                }

                // Structs create a type binding. If they're tuple-like or
                // unit-like structs, they create a value binding too.
                item_struct(ref struct_def, _) => {
                    self.register_type(item.ident, def_id);

                    if struct_def.fields.len() > 0 &&
                            struct_def.fields[0].kind == unnamed_field {
                        self.register_value(item.ident, def_id);
                    }
                }

                // Foreign modules create module bindings if they're the
                // deprecated named foreign modules or just inject names into
                // the current namespace otherwise.
                item_foreign_mod(ref foreign_mod) => {
                    match foreign_mod.sort {
                        named => {
                            // This goes into the module namespace.
                            let def_id = local_def(item.node);
                            self.register_type(item.ident, def_id);
                        }
                        anonymous => {
                            // Merge all of the foreign module's items in.
                            self.populate_foreign_module(item.ident,
                                                         def_id,
                                                         foreign_mod);
                        }
                    }
                }
            }
        }
    }

    // Internal function to populate a foreign module with the contents of a
    // foreign module item in this crate. (Note that this does not populate
    // external modules; for that, see `populate_external()`.)
    priv fn populate_foreign_module(&mut self,
                                    resolver: &mut Resolver,
                                    foreign_mod: &foreign_mod) {
        for foreign_mod.items.each |foreign_item| {
            match foreign_item.node {
                // This is the only branch of this match, but it's included
                // anyway to remind us to update if new foreign items appear.
                foreign_item_fn(*) | foreign_item_const(*) => {
                    let did = local_def(foreign_item.id);
                    self.register_value(foreign_item.ident, did);
                }
            }
        }
    }
}

//
// The `pub use` graph. This tracks which moduloids `pub use` one another.
//

struct PubUseGraph {
    // The vertices of the graph, consisting of the moduloids in the module
    // graph that contain or are the target of `pub use` directives.
    moduloids: LinearMap<def_id,()>,

    // The outgoing edges of the graph. An edge exists between moduloids A
    // and B if moduloid A `pub use`s anything from moduloid B.
    outgoing_edges: LinearMap<def_id,@mut ~[def_id]>,
    incoming_edges: LinearMap<def_id,@mut ~[def_id]>
}

impl PubUseGraph {
    static fn new() -> PubUseGraph {
        PubUseGraph {
            moduloids: LinearMap(),
            outgoing_edges: LinearMap(),
            incoming_edges: LinearMap()
        }
    }

    fn populate(&mut self, resolver: &mut Resolver) {
        do resolver.visit_moduloids_with_view_items |source_did, view_items| {
            for view_items.each |view_item| {
                // We only care about `pub use`.
                if view_item.vis != public {
                    loop;
                }

                match view_item.node {
                    view_item_import(view_paths) => {
                        for view_paths.each |view_path| {
                            let def_id_opt =
                                resolver.resolve_module_part_of_view_path(
                                    source_did,
                                    view_path);
                            match def_id_opt {
                                None => {
                                    // Error was reported. Nothing to do.
                                }
                                Some(def_id) => {
                                    // Add this edge to the graph.
                                    self.moduloids.insert(source_did, ());
                                    self.moduloids.insert(def_id, ());
                                    self.outgoing_edges.insert(
                                        source_did, def_id);
                                    self.incoming_edges.insert(
                                        def_id, source_did);
                                }
                            }
                        }
                    }
                    view_item_use(*) | view_item_export(*) => {}
                }
            }
        }
    }

    fn sort(&mut self) {}       // XXX
}

//
// The main resolver object
//

struct Resolver {
    session: Session,
    ast_map: ast_map::map,
    lang_items: LanguageItems,
    crate: crate,
}

impl Resolver {
    static pub fn new(session: Session,
                      lang_items: LanguageItems,
                      crate: @crate)
                   -> Resolver {
        Resolver {
            session: session,
            lang_items: lang_items,
            crate: crate,
        }
    }

    pub fn resolve(&mut self) {
        // First, find all `pub use` directives and resolve them.
        let pub_use_graph = PubUseGraph::new();
        pub_use_graph.populate(self);
        pub_use_graph.sort();
        self.pub_use_graph = Some(pub_use_graph);
    }

    //
    // Import resolution
    //

    // Visits all the moduloids in the crate that have view items.
    // This function uses some unsafe code under the hood to bridge the
    // mismatch between @fns and &fns.
    fn visit_moduloids_with_view_items(&mut self, f: ModuloidVisitor)) {
        unsafe {
            let this_ptr: c_void = transmute(self);
            let f_ptr: (c_void, c_void) = transmute(f);
            let visitor = visit::mk_vt(@{
                visit_item: |item, _, visitor| {
                    let this: &mut Resolver = transmute(this_ptr);
                    let f: ModuloidVisitor = transmute(f_ptr);
                    let maybe_yield: &fn(&[view_item]) = |view_items| {
                        if view_items.len() > 0 {
                            let did = local_def(item.node.id);
                            let moduloid = Moduloid::get(this, did);
                            f(moduloid, view_items);
                        }
                    }
                    match item.node {
                        item_mod(module) => {
                            maybe_yield(module.node.view_items);
                        }
                        item_foreign_mod(foreign_mod) => {
                            maybe_yield(foreign_mod.node.view_items);
                        }
                        item_const(*) | item_fn(*) | item_ty(*) |
                        item_enum(*) | item_struct(*) | item_trait(*) |
                        item_impl(*) | item_mac(*) => {}
                    }
                    visit::visit_item(item, (), visitor)
                },
                visit_block: |block, _, visitor| {
                    if block.node.view_items.len() > 0 {
                        let did = local_def(block.node.id);
                        let moduloid = Moduloid::get(this, did);
                        f(moduloid, block.node.view_items)
                    }
                    visit::visit_block(block, (), visitor)
                },
                ..*visit::default_visitor()
            });
        }
    }

    // Resolves the module part of a view path; e.g. in `use foo::bar::baz`,
    // this resolves `foo::bar`. Returns the def ID of the moduloid that this
    // refers to, if the module was successfully resolved; otherwise, calls
    // the condition handler and returns `None`.
    fn resolve_module_part_of_view_path(source_def_id: def_id,
                                        view_path: view_path)
                                     -> Option<def_id> {
        let path = match view_path.node {
            view_path_simple(_, ref path, _, _) |
            view_path_glob(ref path, _) |
            view_path_list(ref path, _, _) => path
        };

        // Start at the root of the crate, and process each item in turn.
        // This only looks through direct children of moduloids (and `pub
        // use` results, if that pass has already run).
        //
        // XXX: Support `self` and `super`.
        let mut current = Moduloid::get_root(self);
        for path.idents.each |ident| {
            match current.lookup_module(current) {
                None => {
                    unresolved_err::cond.raise(path.span, current.def_id);
                    return None;
                }
                Some(new_def_id) => {
                    current = Moduloid::get(self, new_def_id);
                }
            }
        }
        return Some(current.def_id);
    }
}

// Entry point to crate resolution.
fn resolve_crate(session: Session,
                 ast_map: ast_map::map,
                 lang_items: LanguageItems,
                 crate: @crate) {
              -> ResolveResult {
    let mut resolver = Resolver::new(session, lang_items, crate);
    resolver.resolve();
    /*{
        def_map: resolver.def_map,
        exp_map2: resolver.export_map2,
        trait_map: resolver.trait_map
    }*/
}

