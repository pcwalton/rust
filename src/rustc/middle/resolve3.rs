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

enum namespace {
    ns_module,
    ns_type,
    ns_value
}

enum namespace_result {
    nsr_unknown,
    nsr_unbound,
    nsr_bound(@graph_node)
}

type namespace_bindings = hashmap<str,@dvec<binding>>;
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

class import_resolution {
    // The number of outstanding references to this name. When this reaches
    // zero, outside modules can count on the targets being correct. Before
    // then, all bets are off; future imports could override this name.
    let mut outstanding_references: uint;

    let mut module_target: option<@graph_node>;
    let mut value_target: option<@graph_node>;
    let mut type_target: option<@graph_node>;

    new() {
        self.outstanding_references = 0u;

        self.module_target = none;
        self.value_target = none;
        self.type_target = none;
    }

    fn target_for_namespace(namespace: namespace) -> option<@graph_node> {
        alt namespace {
            ns_module { ret self.module_target; }
            ns_type   { ret self.type_target;   }
            ns_value  { ret self.value_target;  }
        }
    }
}

#[doc="One node in the tree of modules."]
class module_node {
    let parent_graph_node: @graph_node;

    let children: hashmap<atom,@graph_node>;
    let imports: dvec<@import_directive>;

    // The status of resolving each import in this module.
    let import_resolutions: hashmap<atom,@import_resolution>;

    // The number of unresolved globs that this module exports.
    let mut glob_count: uint;

    // The index of the import we're resolving.
    let mut resolved_import_count: uint;

    new(parent_graph_node: @graph_node) {
        self.parent_graph_node = parent_graph_node;

        self.children = atom_hashmap();
        self.imports = dvec();

        self.import_resolutions = atom_hashmap();
        self.glob_count = 0u;
        self.resolved_import_count = 0u;
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

    fn defined_in_namespace(namespace: namespace) -> bool {
        alt namespace {
            ns_module { ret self.module_def != md_none; }
            ns_type   { ret self.type_def != none;      }
            ns_value  { ret self.value_def != none;     }
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

// FIXME: resolve_result<T>, please

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

    // The number of imports that are currently unresolved.
    let mut unresolved_imports: uint;

    let module_namespace: namespace_bindings;
    let type_namespace: namespace_bindings;
    let value_namespace: namespace_bindings;

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

        self.unresolved_imports = 0u;

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
    fn record_local_name(namespace: namespace_bindings, name: str,
                         id: node_id) {
        ret self.record_global_name(namespace, name, local_def(id));
    }

    fn resolve(this: @resolver) {
        self.build_reduced_graph(this);
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
    fn build_reduced_graph(this: @resolver) {
        visit_crate(*self.crate, self.graph_root, mk_vt(@{
            visit_item: {
                |item, parent_node, visitor|
                (*this).build_reduced_graph_for_item(item, parent_node,
                                                     visitor)
            },
            visit_view_item: {
                |view_item, parent_node, visitor|
                (*this).build_reduced_graph_for_view_item(view_item,
                                                          parent_node,
                                                          visitor)
            }
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

                    // Build up the import directives.
                    let module_node = (*parent_node).get_module();
                    alt view_path.node {
                        view_path_simple(binding, full_path, _) {
                            let target_atom =
                                (*self.atom_table).intern(binding);
                            let source_atom =
                                (*self.atom_table).intern(full_path.
                                                       idents.last());
                            let subclass = @ids_single(target_atom,
                                                       source_atom);
                            self.build_import_directive(module_node,
                                                        module_path,
                                                        subclass);
                        }
                        view_path_list(_, source_idents, _) {
                            for source_idents.each {
                                |source_ident|
                                let name = source_ident.node.name;
                                let atom = (*self.atom_table).intern(name);
                                let subclass = @ids_single(atom, atom);
                                self.build_import_directive(module_node,
                                                            module_path,
                                                            subclass);
                            }
                        }
                        view_path_glob(_, _) {
                            self.build_import_directive(module_node,
                                                        module_path,
                                                        @ids_glob);
                        }
                    }
                }
            }
            view_item_export(*) { /* TODO */ }
            view_item_use(*) { /* Ignore. */ }
        }
    }

    #[doc="Creates and adds an import directive to the given module."]
    fn build_import_directive(module_node: @module_node,
                              module_path: @dvec<atom>,
                              subclass: @import_directive_subclass) {
        let directive = @import_directive(module_path, subclass);
        module_node.imports.push(directive);

        // Bump the reference count on the name. Or, if this is a glob, set
        // the appropriate flag.
        alt *subclass {
            ids_single(target, _) {
                alt module_node.import_resolutions.find(target) {
                    some(resolution) {
                        resolution.outstanding_references += 1u;
                    }
                    none {
                        let resolution = @import_resolution();
                        resolution.outstanding_references = 1u;
                        module_node.import_resolutions.insert(target,
                                                              resolution);
                            
                    }
                }
            }
            ids_glob {
                // Set the glob flag. This tells us that we don't know the
                // module's exports ahead of time.
                module_node.glob_count += 1u;
            }
        }

        self.unresolved_imports += 1u;
    }

    //
    // Import resolution
    //
    // This is a fixed-point algorithm. We resolve imports until our efforts
    // are stymied by an unresolved import; then we bail out of the current
    // module and continue. We terminate successfully once no more imports
    // remain or unsuccessfully when no forward progress in resolving imports
    // is made.
    //

    #[doc="
        Resolves all imports for the crate. This method performs the fixed-
        point iteration.
    "]
    fn resolve_imports() {
        let mut i = 0u;
        let mut prev_unresolved_imports = 0u;
        loop {
            #debug("(resolving imports) iteration %u, %u imports left",
                   i, self.unresolved_imports);

            let module_root = (*self.graph_root).get_module();
            self.resolve_imports_for_module_subtree(module_root);

            if self.unresolved_imports == 0u {
                #debug("(resolving imports) success");
                break;
            }

            if self.unresolved_imports == prev_unresolved_imports {
                #debug("!!! (resolving imports) failure");
                self.report_unresolved_imports(self.graph_root);
                break;
            }

            i += 1u;
            prev_unresolved_imports = self.unresolved_imports;
        }
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
    }

    #[doc="
        Attempts to resolve the given import. The return value indicates
        failure if we're certain the name does not exist, indeterminate if we
        don't know whether the name exists at the moment due to other
        currently-unresolved imports, or success if we know the name exists. If
        successful, the resolved bindings are written into the module.
    "]
    fn resolve_import_for_module(module_node: @module_node,
                                 import_directive: @import_directive)
            -> resolve_import_for_module_result {

        let mut resolution_result;

        // One-level renaming imports of the form `import foo = bar;` are
        // handled specially.
        let module_path = import_directive.module_path;
        if (*module_path).len() == 0u {
            resolution_result =
                self.resolve_one_level_renaming_import(module_node,
                                                       import_directive);
        } else {
            // First, resolve the module path for the directive, if necessary.
            let mut containing_module;
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

            // Next, attempt to resolve the import.
            alt *import_directive.subclass {
                ids_single(target, source) {
                    resolution_result =
                        self.resolve_single_import(module_node,
                                                   containing_module, target,
                                                   source);
                }
                ids_glob {
                    resolution_result =
                        self.resolve_glob_import(module_node,
                                                 containing_module);
                }
            }
        }

        // Decrement the count of unresolved imports.
        alt resolution_result {
            rifmr_success {
                assert self.unresolved_imports >= 1u;
                self.unresolved_imports -= 1u;
            }
            _ { /* Nothing to do here; just return the error. */ }
        }
        ret resolution_result;
    }

    fn resolve_single_import(module_node: @module_node,
                             containing_module: @module_node,
                             target: atom, source: atom)
            -> resolve_import_for_module_result {

        // We need to resolve all three namespaces for this to succeed.
        let mut module_result = nsr_unbound;
        let mut value_result = nsr_unbound;
        let mut type_result = nsr_unbound;

        // Search for direct children of the containing module.
        alt containing_module.children.find(target) {
            none { /* Continue. */ }
            some(child_graph_node) {
                if (*child_graph_node).defined_in_namespace(ns_module) {
                    module_result = nsr_bound(child_graph_node);
                }
                if (*child_graph_node).defined_in_namespace(ns_value) {
                    value_result = nsr_bound(child_graph_node);
                }
                if (*child_graph_node).defined_in_namespace(ns_type) {
                    type_result = nsr_bound(child_graph_node);
                }
            }
        }

        // If we didn't find all three results, search imports.
        alt (module_result, value_result, type_result) {
            (nsr_bound(_), nsr_bound(_), nsr_bound(_)) {
                // Continue.
            }
            _ {
                // If there is an unresolved glob at this point in the
                // containing module, bail out. We don't know enough to be able
                // to resolve this import.
                if containing_module.glob_count > 0u {
                    #debug("(resolving single import) unresolved glob; \
                            bailing out");
                    ret rifmr_indeterminate;
                }

                // Now search the exported imports within the containing
                // module.
                alt containing_module.import_resolutions.find(target) {
                    none {
                        // The containing module definitely doesn't have an
                        // exported import with the name in question. We can
                        // therefore accurately report that the names are
                        // unbound.
                        if module_result == nsr_unknown {
                            module_result = nsr_unbound;
                        }
                        if value_result == nsr_unknown {
                            value_result = nsr_unbound;
                        }
                        if type_result == nsr_unknown {
                            type_result = nsr_unbound;
                        }
                    }
                    some(import_resolution)
                            if import_resolution.outstanding_references == 0u {
                        fn get_binding(import_resolution: @import_resolution,
                                       namespace: namespace)
                                    -> namespace_result {
                            alt (*import_resolution).
                                    target_for_namespace(namespace) {
                                none {
                                    ret nsr_unbound;
                                }
                                some(binding) {
                                    ret nsr_bound(binding);
                                }
                            }
                        }

                        // The name is an import which has been fully resolved.
                        // We can, therefore, just follow the import.
                        if module_result == nsr_unknown {
                            module_result = get_binding(import_resolution,
                                                        ns_module);
                        }
                        if value_result == nsr_unknown {
                            value_result = get_binding(import_resolution,
                                                       ns_type);
                        }
                        if type_result == nsr_unknown {
                            type_result = get_binding(import_resolution,
                                                      ns_value);
                        }
                    }
                    some(_) {
                        // The import is unresolved. Bail out.
                        #debug("(resolving single import) unresolved import; \
                                bailing out");
                        ret rifmr_indeterminate;
                    }
                }
            }
        }

        // We've successfully resolved the import. Write the results in.
        assert module_node.import_resolutions.contains_key(target);
        let import_resolution = module_node.import_resolutions.get(target);

        alt module_result {
            nsr_bound(binding) {
                import_resolution.module_target = some(binding);
            }
            nsr_unbound { /* Continue. */ }
            nsr_unknown { fail "module result should be known at this point"; }
        }
        alt value_result {
            nsr_bound(binding) {
                import_resolution.value_target = some(binding);
            }
            nsr_unbound { /* Continue. */ }
            nsr_unknown { fail "value result should be known at this point"; }
        }
        alt type_result {
            nsr_bound(binding) {
                import_resolution.type_target = some(binding);
            }
            nsr_unbound { /* Continue. */ }
            nsr_unknown { fail "type result should be known at this point"; }
        }

        assert import_resolution.outstanding_references >= 1u;
        import_resolution.outstanding_references -= 1u;

        #debug("(resolving single import) successfully resolved import");
        ret rifmr_success;
    }

    #[doc="
        Resolves a glob import. Note that this function cannot fail; it either
        succeeds or bails out (as importing * from an empty module or a module
        that exports nothing is valid).
    "]
    fn resolve_glob_import(module_node: @module_node,
                           containing_module: @module_node)
            -> resolve_import_for_module_result {

        // This function works in a highly imperative manner; it eagerly adds
        // everything it can to the list of import resolutions of the module
        // node.

        // We must bail out if the node has unresolved imports of any kind
        // (including globs).
        if !(*containing_module).all_imports_resolved() {
            #debug("(resolving glob import) target module has unresolved \
                    imports; bailing out");
            ret rifmr_indeterminate;
        }

        assert containing_module.glob_count == 0u;

        // Add all resolved imports from the containing module.
        for containing_module.import_resolutions.each {
            |atom, target_import_resolution|

            // Here we merge two import resolutions.
            alt module_node.import_resolutions.find(atom) {
                none {
                    // Simple: just copy the old import resolution.
                    let new_import_resolution = @import_resolution();
                    new_import_resolution.module_target =
                        target_import_resolution.module_target;
                    new_import_resolution.value_target =
                        target_import_resolution.value_target;
                    new_import_resolution.type_target =
                        target_import_resolution.type_target;
                    module_node.import_resolutions.insert(atom,
                            new_import_resolution);
                }
                some(dest_import_resolution) {
                    // Merge the two import resolutions at a finer-grained
                    // level.
                    alt target_import_resolution.module_target {
                        none { /* Continue. */ }
                        some(module_target) {
                            dest_import_resolution.module_target =
                                some(module_target);
                        }
                    }
                    alt target_import_resolution.value_target {
                        none { /* Continue. */ }
                        some(value_target) {
                            dest_import_resolution.value_target =
                                some(value_target);
                        }
                    }
                    alt target_import_resolution.type_target {
                        none { /* Continue. */ }
                        some(type_target) {
                            dest_import_resolution.type_target =
                                some(type_target);
                        }
                    }
                }
            }
        }

        // Add all children from the containing module.
        for containing_module.children.each {
            |atom, graph_node|

            let mut dest_import_resolution;
            alt module_node.import_resolutions.find(atom) {
                none {
                    // Create a new import resolution from this child.
                    dest_import_resolution = @import_resolution();
                    module_node.import_resolutions.insert(atom,
                            dest_import_resolution);
                }
                some(existing_import_resolution) {
                    dest_import_resolution = existing_import_resolution;
                }
            }

            // Merge the child item into the import resolution.
            if (*graph_node).defined_in_namespace(ns_module) {
                dest_import_resolution.module_target = some(graph_node);
            }
            if (*graph_node).defined_in_namespace(ns_value) {
                dest_import_resolution.value_target = some(graph_node);
            }
            if (*graph_node).defined_in_namespace(ns_type) {
                dest_import_resolution.type_target = some(graph_node);
            }
        }

        assert module_node.glob_count >= 1u;
        module_node.glob_count -= 1u;

        #debug("(resolving glob import) successfully resolved import");
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

        #debug("(resolving module path for import) processing '%s' rooted at \
               '%s'",
               (*self.atom_table).atoms_to_str(module_path),
               self.module_to_str(module_node));

        // The first element of the module path must be in the current scope
        // chain.
        let first_element = (*module_path).get_elt(0u);
        let mut search_module;
        alt self.resolve_module_in_lexical_scope(module_node, first_element) {
            rmpfir_failed {
                #error("(resolving module path for import) !!! unresolved \
                        name: %s",
                       (*self.atom_table).atom_to_str(first_element));
                ret rmpfir_failed;
            }
            rmpfir_indeterminate {
                #debug("(resolving module path for import) indeterminate; \
                        bailing");
                ret rmpfir_indeterminate;
            }
            rmpfir_success(resulting_module) {
                search_module = resulting_module;
            }
        }

        // Now resolve the rest of the path. This does not involve looking
        // upward though scope chains; we simply resolve names directly in
        // modules as we go.
        let mut index = 1u;
        while index < module_path_len {
            let name = (*module_path).get_elt(index);
            alt self.resolve_name_in_module(search_module, name, ns_module) {
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

    fn resolve_item_in_lexical_scope(module_node: @module_node, name: atom,
                                     namespace: namespace)
            -> resolve_name_in_module_result {
        // The current module node is handled specially. First, check for
        // its immediate children.
        alt module_node.children.find(name) {
            some(graph_node) if (*graph_node).defined_in_namespace(namespace) {
                ret rnimr_success(graph_node);
            }
            some(_) | none { /* Not found; continue. */ }
        }

        // Now check for its import directives. We don't have to have resolved
        // all its imports in the usual way; this is because chains of adjacent
        // import statements are processed as though they mutated the current
        // scope.
        alt module_node.import_resolutions.find(name) {
            none { /* Not found; continue. */ }
            some(import_resolution) {
                alt (*import_resolution).target_for_namespace(namespace) {
                    none { /* Not found; continue. */ }
                    some(target_graph_node) {
                        ret rnimr_success(target_graph_node);
                    }
                }
            }
        }
        
        // Finally, proceed up the scope chain looking for parent modules.
        let mut search_module = module_node;
        loop {
            // Go to the next parent.
            alt search_module.parent_graph_node.parent_node {
                none {
                    // No more parents. This module was unresolved.
                    #debug("(resolving item in lexical scope) unresolved \
                            module");
                    ret rnimr_failed;
                }
                some(gnh_graph_node(parent_node)) {
                    alt (*parent_node).get_module_if_available() {
                        none {
                            // The parent is not a module. This should not
                            // happen.
                            #error("!!! (resolving item in lexical scope) \
                                    UNEXPECTED: parent is not a module");
                            ret rnimr_failed;
                        }
                        some(parent_module_node) {
                            search_module = parent_module_node;
                        }
                    }
                }
            }

            // Resolve the name in the parent module.
            alt self.resolve_name_in_module(search_module, name, namespace) {
                rnimr_failed {
                    // Continue up the search chain.
                }
                rnimr_indeterminate {
                    // We couldn't see through the higher scope because of an
                    // unresolved import higher up. Bail.
                    #debug("(resolving item in lexical scope) indeterminate \
                            higher scope; bailing");
                    ret rnimr_indeterminate;
                }
                rnimr_success(graph_node) {
                    // We found the module.
                    ret rnimr_success(graph_node);
                }
            }
        }
    }

    fn resolve_module_in_lexical_scope(module_node: @module_node, name: atom)
            -> resolve_module_path_for_import_result {
        alt self.resolve_item_in_lexical_scope(module_node, name, ns_module) {
            rnimr_success(graph_node) {
                alt (*graph_node).get_module_if_available() {
                    some(target_module_node) {
                        #debug("(resolving module in lexical scope) found");
                        ret rmpfir_success(target_module_node);
                    }
                    none {
                        #error("!!! (resolving module in lexical scope) module
                                wasn't actually a module!");
                        ret rmpfir_failed;
                    }
                }
            }
            rnimr_indeterminate {
                #debug("(resolving module in lexical scope) indeterminate; \
                        bailing");
                ret rmpfir_indeterminate;
            }
            rnimr_failed {
                #debug("(resolving module in lexical scope) failed to \
                        resolve");
                ret rmpfir_failed;
            }
        }
    }

    #[doc="
        Attempts to resolve the supplied name in the given module for the
        given namespace. If successful, returns the reduced graph node
        corresponding to the name.
    "]
    fn resolve_name_in_module(module_node: @module_node, name: atom,
                              namespace: namespace) ->
            resolve_name_in_module_result {
        #debug("(resolving name in module) resolving '%s' in '%s'",
               (*self.atom_table).atom_to_str(name),
               self.module_to_str(module_node));

        // First, check the direct children of the module.
        alt module_node.children.find(name) {
            some(child_node) if (*child_node).defined_in_namespace(namespace) {
                #debug("(resolving name in module) found node as child");
                ret rnimr_success(child_node);
            }
            some(_) | none {
                // Continue.
            }
        }

        // Next, check the module's imports. If the module has a glob, then
        // we bail out; we don't know its imports.
        if module_node.glob_count > 0u {
            #debug("(resolving name in module) module has glob; bailing out");
            ret rnimr_indeterminate;
        }

        // Otherwise, we check the list of resolved imports.
        alt module_node.import_resolutions.find(name) {
            some(import_resolution) {
                if import_resolution.outstanding_references != 0u {
                    #debug("(resolving name in module) import unresolved; \
                            bailing out");
                    ret rnimr_indeterminate;
                }

                alt (*import_resolution).target_for_namespace(namespace) {
                    none { /* Continue. */ }
                    some(target) {
                        #debug("(resolving name in module) resolved to \
                                import");
                        ret rnimr_success(target);
                    }
                }
            }
            none {
                // Continue.
            }
        }

        // We're out of luck.
        #debug("(resolving name in module) failed to resolve %s",
               (*self.atom_table).atom_to_str(name));
        ret rnimr_failed;
    }

    #[doc="
        Resolves a one-level renaming import of the kind `import foo = bar;`
        This needs special handling, as, unlike all of the other imports, it
        needs to look in the scope chain for modules and non-modules alike.
    "]
    fn resolve_one_level_renaming_import(module_node: @module_node,
                                         import_directive: @import_directive)
            -> resolve_import_for_module_result {

        let mut target_name;
        let mut source_name;
        alt *import_directive.subclass {
            ids_single(target, source) {
                target_name = target;
                source_name = source;
            }
            ids_glob {
                fail "found `import *`, which is invalid";
            }
        }

        #debug("(resolving one-level naming result) resolving import '%s' = \
                '%s'",
                (*self.atom_table).atom_to_str(target_name),
                (*self.atom_table).atom_to_str(source_name));

        // Find the matching items in the lexical scope chain for every
        // namespace. If any of them come back indeterminate, this entire
        // import is indeterminate.
        let mut module_result;
        #debug("(resolving one-level naming result) searching for module");
        alt self.resolve_item_in_lexical_scope(module_node, source_name,
                                               ns_module) {
            rnimr_failed {
                #debug("(resolving one-level renaming import) didn't find \
                        module result");
                module_result = none;
            }
            rnimr_indeterminate {
                #debug("(resolving one-level renaming import) module result \
                        is indeterminate; bailing");
                ret rifmr_indeterminate;
            }
            rnimr_success(graph_node) {
                #debug("(resolving one-level renaming import) module result \
                        found");
                module_result = some(graph_node);
            }
        }

        let mut value_result;
        #debug("(resolving one-level naming result) searching for value");
        alt self.resolve_item_in_lexical_scope(module_node, source_name,
                                               ns_value) {
            rnimr_failed {
                #debug("(resolving one-level renaming import) didn't find \
                        value result");
                value_result = none;
            }
            rnimr_indeterminate {
                #debug("(resolving one-level renaming import) value result is \
                        indeterminate; bailing");
                ret rifmr_indeterminate;
            }
            rnimr_success(graph_node) {
                #debug("(resolving one-level renaming import) value result \
                        found");
                value_result = some(graph_node);
            }
        }

        let mut type_result;
        #debug("(resolving one-level naming result) searching for type");
        alt self.resolve_item_in_lexical_scope(module_node, source_name,
                                               ns_type) {
            rnimr_failed {
                #debug("(resolving one-level renaming import) didn't find \
                        type result");
                type_result = none;
            }
            rnimr_indeterminate {
                #debug("(resolving one-level renaming import) type result is \
                        indeterminate; bailing");
                ret rifmr_indeterminate;
            }
            rnimr_success(graph_node) {
                #debug("(resolving one-level renaming import) type result \
                        found");
                type_result = some(graph_node);
            }
        }

        // If nothing at all was found, that's an error.
        if module_result.is_none() && value_result.is_none() &&
                type_result.is_none() {
            #error("!!! (resolving one-level renaming import) couldn't find \
                    anything with that name");
            ret rifmr_failed;
        }

        // Otherwise, proceed and write in the bindings.
        alt module_node.import_resolutions.find(target_name) {
            none {
                fail "(resolving one-level renaming import) reduced graph \
                      construction or glob importing should have created the \
                      import resolution name by now";
            }
            some(import_resolution) {
                import_resolution.module_target = module_result;
                import_resolution.value_target = value_result;
                import_resolution.type_target = type_result;
            }
        }

        #debug("(resolving one-level renaming import) successfully resolved");
        ret rifmr_success;
    }

    fn report_unresolved_imports(graph_node: @graph_node) {
        let mut module_node;
        alt (*graph_node).get_module_if_available() {
            none { ret; }
            some(associated_module_node) {
                module_node = associated_module_node;
            }
        }

        let import_count = module_node.imports.len();
        uint::range(module_node.resolved_import_count, import_count) {
            |index|
            let module_path = module_node.imports.get_elt(index).module_path;
            #error("!!! unresolved import in %s: %s",
                   self.module_to_str(module_node),
                   (*self.atom_table).atoms_to_str(module_path));
        }

        // Descend into children.
        for module_node.children.each {
            |_name, child_node|
            self.report_unresolved_imports(child_node);
        }
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
    fn record_global_name(namespace: namespace_bindings, name: str,
                          id: def_id) {
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
    let resolver = @resolver(session, ast_map, crate);
    (*resolver).resolve(resolver);
    ret { def_map: resolver.def_map, impl_map: resolver.impl_map };
}

