import driver::session::session;
import syntax::ast::{ _mod, arm, blk, crate, def, def_const, def_fn, def_id };
import syntax::ast::{ def_ty, expr, expr_fn, expr_fn_block, expr_path, ident };
import syntax::ast::{ item, item_class, item_const, item_enum, item_fn };
import syntax::ast::{ item_iface, item_impl, item_mod, item_native_mod };
import syntax::ast::{ item_res, item_ty, native_item_fn, node_id, pat };
import syntax::ast::{ pat_ident, view_item, view_item_export };
import syntax::ast::{ view_item_import, view_item_use, view_path_glob };
import syntax::ast::{ view_path_list, view_path_simple };
import syntax::ast_util::{ local_def, walk_pat };
import syntax::codemap::span;
import syntax::visit::{ default_visitor, fk_method, mk_vt, visit_block };
import syntax::visit::{ visit_crate, visit_expr_opt, visit_fn, visit_item };
import syntax::visit::{ visit_mod, visit_native_item, visit_ty, vt };
import dvec::{ dvec, extensions };
import std::list::list;
import std::map::{ hashmap, int_hash, str_hash };
import ast_map_t = syntax::ast_map::map;

type def_map = hashmap<node_id, def>;
type impl_map = hashmap<node_id, iscopes>;

// Implementation resolution stuff
type method_info = { did: def_id, n_tps: uint, ident: ident};
type _impl = { did: def_id, ident: ident, methods: [@method_info]};
type iscope = @[@_impl];
type iscopes = @list<iscope>;

enum pattern_binding_mode {
    pbm_refutable,
    pbm_irrefutable
}

type namespace = hashmap<str,@dvec<binding>>;
type resolve_visitor = vt<()>;

resource auto_scope(scopes: @dvec<uint>) {
    (*scopes).pop();
}

class binding {
    let scope_id: uint;
    let def_id: def_id;

    new(scope_id: uint, def_id: def_id) {
        self.scope_id = scope_id;
        self.def_id = def_id;
    }
}

class atom {
    let id: uint;

    new(id: uint) {
        self.id = id;
    }

    fn eq(other: atom) -> bool {
        self.id == other.id
    }
}

class atom_table {
    let atoms: hashmap<str,atom>;
    let strings: dvec<str>;
    let mut atom_count: uint;

    new() {
        self.atoms = str_hash();
        self.strings = dvec();
        self.atom_count = 0u;
    }

    fn intern(string: str) -> atom {
        alt self.atoms.find(string) {
            none { /* fall through */ }
            some(atom) { ret atom; }
        }

        let atom = atom(self.atom_count);
        self.atom_count += 1u;
        self.atoms.insert(string, atom);
        self.strings.push(string);

        ret atom;
    }

    fn atom_to_str(atom: atom) -> str {
        ret self.strings.get_elt(atom.id);
    }

    fn atoms_to_str(atoms: @dvec<atom>) -> str {
        // FIXME: Use join and map or something.
        let mut string = "";
        uint::range(0u, (*atoms).len()) {
            |index|
            if index != 0u {
                string += "::";
            }
            string += self.atom_to_str((*atoms).get_elt(index));
        }
        ret string;
    }
}

enum module_def {
    md_none,                    // Does not define a module.
    md_module(@module_node)     // Defines a module with children.
}

#[doc="Creates a hash table of atoms."]
fn atom_hashmap<V:copy>() -> hashmap<atom,V> {
    ret hashmap::<atom,V>({ |a| a.id }, { |a, b| a.eq(b) });
}

#[doc="Contains data for specific types of import directives."]
enum import_directive_subclass {
    ids_single(atom /* target */, atom /* source */),
    ids_multi(@dvec<atom>),
    ids_glob
}

#[doc="One import directive."]
class import_directive {
    let module_path: @dvec<atom>;
    let subclass: @import_directive_subclass;

    new(module_path: @dvec<atom>, subclass: @import_directive_subclass) {
        self.module_path = module_path;
        self.subclass = subclass;
    }
}

#[doc="One node in the tree of modules."]
class module_node {
    let parent_graph_node: @graph_node;

    let children: hashmap<atom,@graph_node>;
    let imports: dvec<@import_directive>;

    // The names that we know to be exported from this module.
    let exported_imports: hashmap<atom,@import_directive>;
    // True if this module exports globs.
    let mut exports_globs: bool;

    // The index of the import we're resolving.
    let mut resolved_import_count: uint;

    // True if we're currently resolving this module.
    let mut marked: bool;

    new(parent_graph_node: @graph_node) {
        self.parent_graph_node = parent_graph_node;

        self.children = atom_hashmap();
        self.imports = dvec();

        self.exported_imports = atom_hashmap();
        self.exports_globs = false;

        self.resolved_import_count = 0u;

        self.marked = false;
    }

    fn all_imports_resolved() -> bool {
        ret self.imports.len() == self.resolved_import_count;
    }
}

// FIXME: This is needed to work around an ICE with classes that refer to
// themselves.
enum graph_node_holder {
    gnh_graph_node(@graph_node)
}

class graph_node {
    // The parent of this node.
    let parent_node: option<graph_node_holder>;

    let mut module_def: module_def;     // Meaning in the module namespace.
    let mut type_def: option<def>;      // Meaning in the type namespace.
    let mut value_def: option<def>;     // Meaning in the value namespace.

    new(parent_node: option<@graph_node>) {
        // FIXME: As above, this is needed to work around an ICE.
        alt parent_node {
            none {
                self.parent_node = none;
            }
            some(graph_node) {
                self.parent_node = some(gnh_graph_node(graph_node));
            }
        }

        self.module_def = md_none;
        self.type_def = none;
        self.value_def = none;
    }

    #[doc="Records a module definition."]
    fn define_module(this: @graph_node) {
        if self.module_def == md_none {
            self.module_def = md_module(@module_node(this));
        }
    }

    #[doc="Records a type definition."]
    fn define_type(def: def) {
        self.type_def = some(def);
    }

    #[doc="Records a value definition."]
    fn define_value(def: def) {
        self.value_def = some(def);
    }

    #[doc="Returns the module node if applicable."]
    fn get_module_if_available() -> option<@module_node> {
        alt self.module_def {
            md_none { ret none; }
            md_module(module_node) { ret some(module_node); }
        }
    }

    #[doc="
        Returns the module node. Fails if this node does not have a module
        definition."
    ]
    fn get_module() -> @module_node {
        alt self.module_def {
            md_none {
                fail "get_module called on a node with no module definition!";
            }
            md_module(module_node) {
                ret module_node;
            }
        }
    }

    // FIXME: Shouldn't have a this parameter. Use an impl instead. Thought
    // this might have been the cause of an ICE, but I don't think it is.
    #[doc="
        Adds a new child item to the module definition of this node and returns
        it.

        If this node does not have a module definition, fails.
    "]
    fn add_child(this: @graph_node, atom: atom) -> @graph_node {
        alt self.module_def {
            md_none { fail "Can't add a child to a non-module definition!"; }
            md_module(module_node) {
                alt module_node.children.find(atom) {
                    none {
                        let child = @graph_node(some(this));
                        module_node.children.insert(atom, child);
                        ret child;
                    }
                    some(child) {
                        ret child;
                    }
                }
            }
        }
    }
}

enum resolve_module_path_for_import_result {
    rmpfir_failed,                  // Failed to resolve the name.
    rmpfir_indeterminate,           // Couldn't determine; unresolved glob.
    rmpfir_success(@module_node)    // Success.
}

enum resolve_name_in_module_result {
    rnimr_failed,               // Failed to resolve the name.
    rnimr_indeterminate,        // Couldn't determine due to unresolved glob.
    rnimr_success(@graph_node)  // Success.
}

enum resolve_import_for_module_result {
    rifmr_failed,           // Failed to resolve the name.
    rifmr_indeterminate,    // Couldn't determine due to unresolved glob.
    rifmr_success           // Success. Result is stored in the import.
}

#[doc="The main resolver class."]
class resolver {
    let session: session;
    let ast_map: ast_map_t;
    let crate: @crate;

    let atom_table: @atom_table;

    let graph_root: @graph_node;

    let module_namespace: namespace;
    let type_namespace: namespace;
    let value_namespace: namespace;

    let scope_ids: hashmap<node_id,uint>;
    let mut next_scope_id: uint;
    let scopes: @dvec<uint>;

    let def_map: def_map;
    let impl_map: impl_map;

    new(session: session, ast_map: ast_map_t, crate: @crate) {
        self.session = session;
        self.ast_map = ast_map;
        self.crate = crate;

        self.atom_table = @atom_table();

        self.graph_root = @graph_node(none);
        (*self.graph_root).define_module(self.graph_root);

        self.module_namespace = str_hash();
        self.type_namespace = str_hash();
        self.value_namespace = str_hash();

        self.scope_ids = int_hash();
        self.next_scope_id = 0u;
        self.scopes = @dvec();

        self.def_map = int_hash();
        self.impl_map = int_hash();
    }

    fn new_scope_id() -> uint {
        let id = self.next_scope_id;
        self.next_scope_id += 1u;
        ret id;
    }

    fn new_scope() -> auto_scope {
        (*self.scopes).push(self.new_scope_id());
        ret auto_scope(self.scopes);
    }

    #[doc="
        Binds the supplied name in the supplied namespace to the given node ID
        in this crate.
    "]
    fn record_local_name(namespace: namespace, name: str, id: node_id) {
        ret self.record_global_name(namespace, name, local_def(id));
    }

    fn resolve() {
        self.build_reduced_graph();
        self.resolve_imports();
        self.resolve_crate();
    }

    //
    // Reduced graph building
    //
    // Here we build the "reduced graph": the graph of the module tree without
    // any imports resolved.
    //

    #[doc="Constructs the reduced graph for the entire crate."]
    fn build_reduced_graph() {
        visit_crate(*self.crate, self.graph_root, mk_vt(@{
            visit_item: self.build_reduced_graph_for_item,
            visit_view_item: self.build_reduced_graph_for_view_item
            with *default_visitor()
        }));
    }

    #[doc="Constructs the reduced graph for one item."]
    fn build_reduced_graph_for_item(item: @item, &&parent_node: @graph_node,
                                    &&visitor: vt<@graph_node>) {
        let atom = (*self.atom_table).intern(item.ident);
        let child = (*parent_node).add_child(parent_node, atom);

        alt item.node {
            item_mod(module) {
                (*child).define_module(child);
                visit_mod(module, item.span, item.id, child, visitor);
            }
            item_native_mod(native_module) {
                (*child).define_module(child);
                visit_item(item, child, visitor);
            }

            // These items live in the value namespace.
            item_const(*) {
                (*child).define_value(def_const(local_def(item.id)));
            }
            item_fn(decl, _, _) {
                let def = def_fn(local_def(item.id), decl.purity);
                (*child).define_value(def);
            }

            // These items live in the type namespace.
            item_ty(*) {
                (*child).define_type(def_ty(local_def(item.id)));
            }

            // These items live in both the type and value namespaces.
            item_enum(_variants, _, _) {
                (*child).define_type(def_ty(local_def(item.id)));
                // TODO: Variants.
            }
            item_res(decl, _, _, _, _, _) {
                let purity = decl.purity;
                let value_def = def_fn(local_def(item.id), purity);
                (*child).define_value(value_def);
                (*child).define_type(def_ty(local_def(item.id)));
            }
            item_class(_, _, _, ctor, _, _) {
                (*child).define_type(def_ty(local_def(item.id)));

                let purity = ctor.node.dec.purity;
                let ctor_def = def_fn(local_def(ctor.node.id), purity);
                (*child).define_value(ctor_def);
            }

            item_impl(*) {
                // TODO
            }

            item_iface(*) { /* Ignore. */ }
        }
    }

    #[doc="
        Constructs the reduced graph for one 'view item'. View items consist of
        imports and use directives.
    "]
    fn build_reduced_graph_for_view_item(view_item: @view_item,
                                         &&parent_node: @graph_node,
                                         &&_visitor: vt<@graph_node>) {
        alt view_item.node {
            view_item_import(view_paths) {
                for view_paths.each {
                    |view_path|

                    // Extract and intern the module part of the path. For
                    // globs and lists, the path is found directly in the AST;
                    // for simple paths we have to munge the path a little.

                    let module_path = @dvec();
                    alt view_path.node {
                        view_path_simple(_, full_path, _) {
                            let path_len = full_path.idents.len();
                            assert path_len != 0u;

                            for full_path.idents.eachi {
                                |i, ident|
                                if i != path_len - 1u {
                                    let atom =
                                        (*self.atom_table).intern(ident);
                                    (*module_path).push(atom);
                                }
                            }
                        }

                        view_path_glob(module_ident_path, _) |
                        view_path_list(module_ident_path, _, _) {
                            for module_ident_path.idents.each {
                                |ident|
                                let atom = (*self.atom_table).intern(ident);
                                (*module_path).push(atom);
                            }
                        }
                    }

                    // Build up the subclass.
                    let mut subclass;
                    alt view_path.node {
                        view_path_simple(binding, full_path, _) {
                            let target_atom =
                                (*self.atom_table).intern(binding);
                            let source_atom =
                                (*self.atom_table).intern(full_path.
                                                       idents.last());
                            subclass = @ids_single(target_atom, source_atom);
                        }
                        view_path_glob(_, _) {
                            subclass = @ids_glob;
                        }
                        view_path_list(_, source_idents, _) {
                            let sources = @dvec();
                            for source_idents.each {
                                |source_ident|
                                let atom =
                                    (*self.atom_table).intern(source_ident.
                                                              node.name);
                                (*sources).push(atom);
                            }
                            subclass = @ids_multi(sources);
                        }
                    }

                    // Create the import directive and add it to the list of
                    // imports for this module.
                    let directive = @import_directive(module_path, subclass);
                    let module_node = (*parent_node).get_module();
                    module_node.imports.push(directive);

                    // If we know the names that this import injects into the
                    // module namespace, add them now. This is the case for
                    // every import subclass except the glob.
                    alt *subclass {
                        ids_single(name, _) {
                            module_node.exported_imports.insert(name,
                                                                directive);
                        }
                        ids_multi(names) {
                            for (*names).each {
                                |name|
                                module_node.exported_imports.insert(name,
                                                                    directive);
                            }
                        }
                        ids_glob {
                            // Set the flag indicating that this module exports
                            // a glob. This tells us that we don't know its
                            // exports at the moment.
                            module_node.exports_globs = true;
                        }
                    }
                }
            }
            view_item_export(*) { /* TODO */ }
            view_item_use(*) { /* Ignore. */ }
        }
    }

    //
    // Import resolution
    //
    // This is a fixed-point algorithm. We greedily follow imports around the
    // crate until our attempts at name resolution are stymied by a glob we
    // haven't resolved yet. In that case we come around again.
    //

    #[doc="
        Resolves all imports for the crate. This method performs the fixed-
        point iteration.
    "]
    fn resolve_imports() {
        #debug("resolving imports, top level");
        let module_root = (*self.graph_root).get_module();
        self.resolve_imports_for_module_subtree(module_root);
    }

    #[doc="
        Attempts to resolve imports for the given module and all of its
        submodules.
    "]
    fn resolve_imports_for_module_subtree(module_node: @module_node) {
        #debug("(resolving imports for module subtree) resolving %s",
               self.module_to_str(module_node));
        self.resolve_imports_for_module(module_node);

        for module_node.children.each {
            |_name, child_node|
            alt (*child_node).get_module_if_available() {
                none { /* Nothing to do. */ }
                some(child_module_node) {
                    #debug("(resolving imports for module subtree) resolving \
                           imports for %s",
                           self.module_to_str(child_module_node));
                    self.resolve_imports_for_module_subtree(child_module_node);
                }
            }
        }
    }

    #[doc="Attempts to resolve imports for the given module only."]
    fn resolve_imports_for_module(module_node: @module_node) {
        if (*module_node).all_imports_resolved() {
            #debug("(resolving imports for module) all imports resolved for \
                   %s", self.module_to_str(module_node));
            ret;
        }

        if module_node.marked {
            #debug("(resolving imports for module) skipping; marked!");
            ret;
        }

        module_node.marked = true;

        let import_count = module_node.imports.len();
        while module_node.resolved_import_count < import_count {
            let import_index = module_node.resolved_import_count;
            let import_directive = module_node.imports.get_elt(import_index);
            alt self.resolve_import_for_module(module_node, import_directive) {
                rifmr_failed {
                    // We presumably emitted an error. Continue.
                }
                rifmr_indeterminate {
                    // Bail out. We'll come around next time.
                    break;
                }
                rifmr_success {
                    // Good. Continue.
                }
            }

            module_node.resolved_import_count += 1u;
        }

        module_node.marked = false;
    }

    #[doc="
        Attempts to resolve the given import. The return value indicates
        failure if we're certain the name does not exist, indeterminate if we
        don't know whether the name exists at the moment due to outstanding
        globs, or success if we know the name exists. If successful, the
        bindings are written into the import directive.
    "]
    fn resolve_import_for_module(module_node: @module_node,
                                 import_directive: @import_directive)
            -> resolve_import_for_module_result {

        // First, resolve the module path for the directive, if necessary.
        let mut containing_module;
        let module_path = import_directive.module_path;
        if (*module_path).len() > 0u {
            alt self.resolve_module_path_for_import(module_node, module_path) {
                rmpfir_failed {
                    ret rifmr_failed;
                }
                rmpfir_indeterminate {
                    ret rifmr_indeterminate;
                }
                rmpfir_success(module_node) {
                    // Continue.
                    containing_module = module_node;
                }
            }
        } else {
            containing_module = module_node;
        }

        // Next, look up the name or names within that module.
        // TODO
        ret rifmr_success;
    }

    #[doc="
        Attempts to resolve the module part of an import directive rooted at
        the given module.
    "]
    fn resolve_module_path_for_import(module_node: @module_node,
                                      module_path: @dvec<atom>)
            -> resolve_module_path_for_import_result {

        let module_path_len = (*module_path).len();
        assert module_path_len > 0u;

        #debug("(resolving module path for import) processing %s rooted at %s",
               (*self.atom_table).atoms_to_str(module_path),
               self.module_to_str(module_node));

        // The first element of the module path must be in the current scope
        // chain.

        let first_element = (*module_path).get_elt(0u);
        let mut search_module = module_node;
        loop {
            let resolve_result = self.resolve_name_in_module(search_module,
                                                             first_element);
            alt resolve_result {
                rnimr_failed {
                    /* Continue. */
                }
                rnimr_indeterminate {
                    #debug("!!! (resolving module path for import) \
                           UNEXPECTED: indeterminate");
                }
                rnimr_success(graph_node) {
                    alt (*graph_node).get_module_if_available() {
                        none {
                            #debug("!!! (resolving module path for import) \
                                   not a module: %s",
                                   (*self.atom_table).
                                        atom_to_str(first_element));
                        }
                        some(module_node) {
                            #debug("(resolving module path for import) \
                                    found: %s",
                                   (*self.atom_table).
                                        atom_to_str(first_element));
                            search_module = module_node;
                            break;
                        }
                    }
                }
            }

            // We didn't find the module at this scope level. Go to the next
            // one.
            alt search_module.parent_graph_node.parent_node {
                none {
                    // No more parents. This module was unresolved.
                    ret rmpfir_failed;
                }
                some(gnh_graph_node(parent_node)) {
                    alt (*parent_node).get_module_if_available() {
                        none {
                            // The parent is not a module. This should not
                            // happen.
                            #debug("!!! (resolving module path for import) \
                                    UNEXPECTED: parent is not a module");
                            ret rmpfir_failed;
                        }
                        some(parent_module_node) {
                            // Continue up to the next parent.
                            search_module = parent_module_node;
                        }
                    }
                }
            }
        }

        // Now resolve the rest of the path. This does not involve looking
        // upward though scope chains; we simply resolve names directly in
        // modules as we go.
        let mut index = 1u;
        while index < module_path_len {
            let name = (*module_path).get_elt(index);
            alt self.resolve_name_in_module(search_module, name) {
                rnimr_failed {
                    #debug("!!! (resolving module path for import) module \
                           resolution failed: %s",
                           (*self.atom_table).atom_to_str(name));
                    ret rmpfir_failed;
                }
                rnimr_indeterminate {
                    #debug("(resolving module path for import) module \
                           resolution is indeterminate: %s",
                           (*self.atom_table).atom_to_str(name));
                    ret rmpfir_indeterminate;
                }
                rnimr_success(graph_node) {
                    alt (*graph_node).get_module_if_available() {
                        none {
                            // Not a module.
                            #debug("!!! (resolving module path for import) \
                                   not a module: %s",
                                   (*self.atom_table).atom_to_str(name));
                            ret rmpfir_failed;
                        }
                        some(resulting_module) {
                            search_module = resulting_module;
                        }
                    }
                }
            }

            index += 1u;
        }

        #debug("(resolving module path for import) resolved module");
        ret rmpfir_success(search_module);
    }

    #[doc="
        Attempts to resolve the supplied name in the given module. If
        successful, returns the reduced graph node corresponding to the name.
    "]
    fn resolve_name_in_module(module_node: @module_node, name: atom) ->
            resolve_name_in_module_result {
        #debug("(resolving name in module) resolving %s in %s",
               (*self.atom_table).atom_to_str(name),
               self.module_to_str(module_node));

        // First, check children.
        alt module_node.children.find(name) {
            some(child_node) {
                #debug("(resolving name in module) found node as child");
                ret rnimr_success(child_node);
            }
            none {
                // Continue.
            }
        }

        // If we've marked this module, then stop here. This prevents us from
        // following cycles forever.
        //
        // In particular, this prevents the otherwise-very-common case of an
        // import following itself.
        if module_node.marked {
            ret rnimr_failed;
        }

        // Next, check known exports.
        alt module_node.exported_imports.find(name) {
            some(import_directive) {
                #debug("(resolving name in module) following import");

                alt self.resolve_import_for_module(module_node,
                                                   import_directive) {
                    rifmr_failed {
                        // Continue.
                    }
                    rifmr_indeterminate {
                        ret rnimr_indeterminate;
                    }
                    rifmr_success {
                        #debug("(resolving name in module) found node as \
                                known export");
                        // TODO
                        //ret rnimr_success(target_node);
                        ret rnimr_failed;
                    }
                }
            }
            none {
                // Continue.
            }
        }

        // Check to see if this name might be covered by a glob. If so, we
        // can't figure it out right now. We'll get to it in a subsequent
        // import resolution pass; for now, bail out.
        //
        // FIXME: We might be able to be a little more precise here; we only
        // have to have all *globs* resolved in the module, not all imports.

        if module_node.exports_globs &&
                !(*module_node).all_imports_resolved() {
            #debug("(resolving name in module) module exports globs; will \
                    return later");
            ret rnimr_indeterminate;
        }

        // The name is not covered by a glob (or all the globs have been
        // resolved). We're out of luck.
        #debug("(resolving name in module) failed to resolve %s",
               (*self.atom_table).atom_to_str(name));
        ret rnimr_failed;
    }

    //
    // AST resolution
    //
    // We proceed by building up a list of scopes. Each scope is simply a hash
    // table. When we find a binding in an outer scope, we cache it in the
    // innermost scope.
    //

    #[doc="
        Binds the supplied name in the supplied namespace to the given node ID
        in any crate.
    "]
    fn record_global_name(namespace: namespace, name: str, id: def_id) {
        let mut bindings;
        alt namespace.find(name) {
            none {
                bindings = @dvec();
                namespace.insert(name, bindings);
            }
            some(existing_bindings) {
                bindings = existing_bindings;
            }
        }

        let binding = binding((*self.scopes).last(), id);
        (*bindings).push(binding);
    }

    fn resolve_crate() {
        visit_crate(*self.crate, (), mk_vt(@{
            visit_item: {
                |item, _context, visitor|
                self.resolve_item(item, visitor);
            },
            visit_arm: {
                |arm, _context, visitor|
                self.resolve_arm(arm, visitor);
            },
            visit_block: {
                |block, _context, visitor|
                self.resolve_block(block, visitor);
            }
            with *default_visitor()
        }));
    }

    fn resolve_item(item: @item, visitor: resolve_visitor) {
        alt item.node {
            item_enum(*) | item_ty(*) {
                let _scope = self.new_scope();
                visit_item(item, (), visitor);
            }
            item_impl(_, _, _, _, methods) {
                // Create a new scope for the impl-wide type parameters.
                let _scope = self.new_scope();

                for methods.each {
                    |method|
                    // We also need a new scope for the method-specific type
                    // parameters.
                    let _scope = self.new_scope();
                    visit_fn(fk_method(method.ident, method.tps, method),
                             method.decl, method.body, method.span, method.id,
                             (), visitor);
                }
            }
            item_iface(_, _, methods) {
                // Create a new scope for the interface-wide type parameters.
                let _scope = self.new_scope();

                for methods.each {
                    |method|
                    // We also need a new scope for the method-specific type
                    // parameters.
                    let _scope = self.new_scope();
                    visit_ty(method.decl.output, (), visitor);
                }
            }
            item_class(*) {
                // Create a new scope for the class-wide type parameters.
                // FIXME: Handle methods properly.
                visit_item(item, (), visitor);
            }
            item_mod(module) {
                let _scope = self.new_scope();
                self.resolve_module(module, item.span, item.ident, item.id,
                                    visitor);
            }
            item_native_mod(native_module) {
                for native_module.items.each {
                    |native_item|
                    alt native_item.node {
                        native_item_fn(*) {
                            let _scope = self.new_scope();
                            visit_native_item(native_item, (), visitor);
                        }
                    }
                }
            }
            item_res(*) | item_fn(*) | item_const(*) {
                visit_item(item, (), visitor);
            }
        }
    }

    fn resolve_module(module: _mod, span: span, name: ident, id: node_id,
                      visitor: resolve_visitor) {
        self.record_local_name(self.module_namespace, name, id);

        let _scope = self.new_scope();
        visit_mod(module, span, id, (), visitor);
    }

    fn resolve_arm(arm: arm, visitor: resolve_visitor) {
        for arm.pats.each {
            |pattern|
            self.resolve_pattern(pattern, pbm_refutable);
        }

        visit_expr_opt(arm.guard, (), visitor);
        self.resolve_block(arm.body, visitor);
    }

    fn resolve_block(block: blk, visitor: resolve_visitor) {
        let _scope = self.new_scope();
        visit_block(block, (), visitor);
    }

    fn resolve_pattern(pattern: @pat, _mode: pattern_binding_mode) {
        walk_pat(pattern) {
            |pattern|
            alt pattern.node {
                pat_ident(path, none)
                        if !path.global && path.idents.len() == 1u {
                    // The meaning of pat_ident with no type parameters depends
                    // on whether an enum variant with that name is in scope.
                    // The probing lookup has to be careful not to emit
                    // spurious errors. Only matching patterns (alt) can match
                    // nullary variants. For binding patterns (let), matching
                    // such a variant is simply disallowed (since it's rarely
                    // what you want).

                    self.record_local_name(self.value_namespace,
                                           path.idents[0], pattern.id);
                }
                _ {
                    /* Nothing to do. FIXME: Handle more cases. */
                }
            }
        }
    }

    fn resolve_expr(expr: @expr, _visitor: resolve_visitor) {
        alt expr.node {
            _ { /* TODO */ }
        }
    }

    // Diagnostics

    #[doc="A terribly inefficient routine to print out the name of a module."]
    fn module_to_str(module_node: @module_node) -> str {
        let atoms = dvec();
        let mut current_node = module_node;
        loop {
            let parent_graph_node = current_node.parent_graph_node;
            alt parent_graph_node.parent_node {
                none {
                    break;
                }
                some(gnh_graph_node(parent_node)) {
                    alt (*parent_node).get_module_if_available() {
                        none {
                            break;
                        }
                        some(parent_module_node) {
                            for parent_module_node.children.each {
                                |name, child_node|
                                if box::ptr_eq(child_node, parent_graph_node) {
                                    atoms.push(name);
                                    break;
                                }
                            }
                            current_node = parent_module_node;
                        }
                    }
                }
            }
        }

        if atoms.len() == 0u {
            ret "???";
        }

        let mut string = "";
        let mut i = atoms.len() - 1u;
        loop {
            if i < atoms.len() - 1u {
                string += "::";
            }
            string += (*self.atom_table).atom_to_str(atoms.get_elt(i));

            if i == 0u {
                break;
            }
            i -= 1u;
        }

        ret string;
    }
}

#[doc="Entry point to crate resolution."]
fn resolve_crate(session: session, ast_map: ast_map_t, crate: @crate)
        -> { def_map: def_map, impl_map: impl_map } {
    let resolver = resolver(session, ast_map, crate);
    resolver.resolve();
    ret { def_map: resolver.def_map, impl_map: resolver.impl_map };
}

