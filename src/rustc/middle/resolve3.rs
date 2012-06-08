import driver::session::session;
import metadata::csearch::{each_path, lookup_defs};
import metadata::cstore::find_use_stmt_cnum;
import metadata::decoder::{def_like, dl_def, dl_field, dl_impl};
import syntax::ast::{_mod, arm, blk, crate, crate_num, def, def_arg};
import syntax::ast::{def_binding, def_class, def_const, def_fn, def_id};
import syntax::ast::{def_local, def_mod, def_native_mod, def_prim_ty};
import syntax::ast::{def_region, def_self, def_ty, def_ty_param, def_upvar};
import syntax::ast::{def_use, def_variant, expr, expr_fn, expr_fn_block};
import syntax::ast::{expr_path, ident, item, item_class, item_const};
import syntax::ast::{item_enum, item_fn, item_iface, item_impl, item_mod};
import syntax::ast::{item_native_mod, item_res, item_ty, native_item_fn};
import syntax::ast::{node_id, pat, pat_ident, view_item, view_item_export};
import syntax::ast::{view_item_import, view_item_use, view_path_glob};
import syntax::ast::{view_path_list, view_path_simple};
import syntax::ast_util::{local_def, walk_pat};
import syntax::codemap::span;
import syntax::visit::{default_visitor, fk_method, mk_vt, visit_block};
import syntax::visit::{visit_crate, visit_expr_opt, visit_fn, visit_item};
import syntax::visit::{visit_mod, visit_native_item, visit_ty, vt};
import dvec::{dvec, extensions};
import std::list::list;
import std::map::{hashmap, int_hash, str_hash};
import str::split_str;
import vec::pop;
import ast_map_t = syntax::ast_map::map;

type def_map = hashmap<node_id, def>;
type impl_map = hashmap<node_id, iscopes>;

// Implementation resolution stuff
type method_info = { did: def_id, n_tps: uint, ident: ident };
type _impl = { did: def_id, ident: ident, methods: [@method_info] };
type iscope = @[@_impl];
type iscopes = @list<iscope>;

enum pattern_binding_mode {
    pbm_refutable,
    pbm_irrefutable
}

enum namespace {
    ns_module,
    ns_type,
    ns_value,
    ns_impl
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

// FIXME (issue 2550): Should be a class but then it becomes not implicitly
// copyable due to a kind bug.
type atom = uint;

fn atom(n: uint) -> atom { ret n; }

class atom_table {
    let atoms: hashmap<@str,atom>;
    let strings: dvec<@str>;
    let mut atom_count: uint;

    new() {
        self.atoms = hashmap::<@str,atom>({ |x| str::hash(*x) },
                                          { |x, y| str::eq(*x, *y) });
        self.strings = dvec();
        self.atom_count = 0u;
    }

    fn intern(string: @str) -> atom {
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

    fn atom_to_str(atom: atom) -> @str {
        ret self.strings.get_elt(atom);
    }

    fn atoms_to_strs(atoms: [atom], f: fn(@str) -> bool) {
        for atoms.each {
            |atom|
            if !f(self.atom_to_str(atom)) {
                ret;
            }
        }
    }

    fn atoms_to_str(atoms: [atom]) -> @str {
        // FIXME: str::connect should do this
        let mut result = "";
        let mut first = true;
        for self.atoms_to_strs(atoms) {
            |string|

            if first {
                first = false;
            } else {
                result += "::";
            }

            result += *string;
        }

        // FIXME: Shouldn't copy here. Need string builder.
        ret @result;
    }
}

enum module_def {
    md_none,                                // Does not define a module.
    md_local_module(@local_module),         // Defines a local module.
    md_external_module(@external_module)    // Defines an external module.
}

#[doc="Creates a hash table of atoms."]
fn atom_hashmap<V:copy>() -> hashmap<atom,V> {
    ret hashmap::<atom,V>({ |a| a }, { |a, b| a == b });
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
    let mut impl_target: option<@graph_node>;

    new() {
        self.outstanding_references = 0u;

        self.module_target = none;
        self.value_target = none;
        self.type_target = none;
        self.impl_target = none;
    }

    fn target_for_namespace(namespace: namespace) -> option<@graph_node> {
        alt namespace {
            ns_module { ret self.module_target; }
            ns_type   { ret self.type_target;   }
            ns_value  { ret self.value_target;  }
            ns_impl   { ret self.impl_target;   }
        }
    }
}

#[doc="One node in the tree of modules."]
class local_module {
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

#[doc="An external module in the graph."]
class external_module {
    let parent_graph_node: @graph_node;
    let mut def_id: option<def_id>;

    let children: hashmap<atom,@graph_node>;

    new(parent_graph_node: @graph_node, def_id: option<def_id>) {
        self.parent_graph_node = parent_graph_node;
        self.def_id = def_id;

        self.children = atom_hashmap();
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
    let mut impl_defs: [def_id];        // Meaning in the impl namespace.

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
        self.impl_defs = [];
    }

    #[doc="Records a local module definition."]
    fn define_local_module(this: @graph_node) {
        if self.module_def == md_none {
            self.module_def = md_local_module(@local_module(this));
        }
    }

    #[doc="Records an external module definition with the given crate ID."]
    fn define_external_module(this: @graph_node, def_id: option<def_id>)
            -> @external_module {
        assert self.module_def == md_none;  // FIXME: should be an error
        let external_module = @external_module(this, def_id);
        self.module_def = md_external_module(external_module);
        ret external_module;
    }

    #[doc="Records a type definition."]
    fn define_type(def: def) {
        self.type_def = some(def);
    }

    #[doc="Records a value definition."]
    fn define_value(def: def) {
        self.value_def = some(def);
    }

    #[doc="Records an impl definition."]
    fn define_impl(def_id: def_id) {
        self.impl_defs += [def_id];
    }

    #[doc="Returns the local module node if applicable."]
    fn get_local_module_if_available() -> option<@local_module> {
        alt self.module_def {
            md_none                       { ret none;               }
            md_local_module(local_module) { ret some(local_module); }
            md_external_module(*)         { ret none;               }
        }
    }

    #[doc="
        Returns the local module node. Fails if this node does not have a
        local module definition.
    "]
    fn get_local_module() -> @local_module {
        alt self.module_def {
            md_none {
                fail "get_local_module called on a node with no module \
                      definition!";
            }
            md_local_module(local_module) {
                ret local_module;
            }
            md_external_module(*) {
                fail "get_local_module called on a node with an external \
                      module definition!";
            }
        }
    }

    #[doc="
        Returns the external module node. Fails if this node does not have an
        external module definition.
    "]
    fn get_external_module() -> @external_module {
        alt self.module_def {
            md_none {
                fail "get_external_module called on a node with no module \
                      definition!";
            }
            md_local_module(*) {
                fail "get_external_module called on a node with a local \
                      module definition!";
            }
            md_external_module(external_module) {
                ret external_module;
            }
        }
    }

    fn defined_in_namespace(namespace: namespace) -> bool {
        alt namespace {
            ns_module { ret self.module_def != md_none; }
            ns_type   { ret self.type_def != none;      }
            ns_value  { ret self.value_def != none;     }
            ns_impl   { ret self.impl_defs.len() >= 0u; }
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
            md_external_module(external_module) {
                alt external_module.children.find(atom) {
                    none {
                        let child = @graph_node(some(this));
                        external_module.children.insert(atom, child);
                        ret child;
                    }
                    some(child) {
                        ret child;
                    }
                }
            }
            md_local_module(local_module) {
                alt local_module.children.find(atom) {
                    none {
                        let child = @graph_node(some(this));
                        local_module.children.insert(atom, child);
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

enum resolve_result<T> {
    rr_failed,          // Failed to resolve the name.
    rr_indeterminate,   // Couldn't determine due to unresolved globs.
    rr_success(T)       // Successfully resolved the import.
}

class name_binding {
    let scope: uint;
    let def_like: def_like;

    new(scope: uint, def_like: def_like) {
        self.scope = scope;
        self.def_like = def_like;
    }
}

class name_bindings {
    let module_bindings: @dvec<@name_binding>;
    let type_bindings: @dvec<@name_binding>;
    let value_bindings: @dvec<@name_binding>;
    let impl_bindings: @dvec<@name_binding>;

    new() {
        self.module_bindings = @dvec();
        self.type_bindings = @dvec();
        self.value_bindings = @dvec();
        self.impl_bindings = @dvec();
    }
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

    let mut next_scope_id: uint;
    let scopes: @dvec<uint>;

    // A mapping from a local name to the set of bindings for that name.
    let mut names: hashmap<atom,@name_bindings>;

    // The graph node that represents the current scope.
    let mut current_graph_node: @graph_node;

    let def_map: def_map;
    let impl_map: impl_map;

    new(session: session, ast_map: ast_map_t, crate: @crate) {
        self.session = session;
        self.ast_map = ast_map;
        self.crate = crate;

        self.atom_table = @atom_table();

        self.graph_root = @graph_node(none);
        (*self.graph_root).define_local_module(self.graph_root);

        self.unresolved_imports = 0u;

        self.next_scope_id = 0u;
        self.scopes = @dvec();

        self.names = atom_hashmap();

        self.current_graph_node = self.graph_root;

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
        let atom =
            (*self.atom_table).intern(@/* FIXME: bad */ copy item.ident);
        let child = (*parent_node).add_child(parent_node, atom);

        alt item.node {
            item_mod(module) {
                (*child).define_local_module(child);
                visit_mod(module, item.span, item.id, child, visitor);
            }
            item_native_mod(native_module) {
                (*child).define_local_module(child);
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
                (*child).define_impl(local_def(item.id));
            }

            item_iface(*) { /* TODO */ }
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
                                        (*self.atom_table).intern
                                            (@copy ident);
                                    (*module_path).push(atom);
                                }
                            }
                        }

                        view_path_glob(module_ident_path, _) |
                        view_path_list(module_ident_path, _, _) {
                            for module_ident_path.idents.each {
                                |ident|
                                let atom =
                                    (*self.atom_table).intern(@copy ident);
                                (*module_path).push(atom);
                            }
                        }
                    }

                    // Build up the import directives.
                    let local_module = (*parent_node).get_local_module();
                    alt view_path.node {
                        view_path_simple(binding, full_path, _) {
                            let target_atom =
                                (*self.atom_table).intern(@copy binding);
                            let source_atom =
                                (*self.atom_table).intern
                                    (@copy full_path.idents.last());
                            let subclass = @ids_single(target_atom,
                                                       source_atom);
                            self.build_import_directive(local_module,
                                                        module_path,
                                                        subclass);
                        }
                        view_path_list(_, source_idents, _) {
                            for source_idents.each {
                                |source_ident|
                                let name = source_ident.node.name;
                                let atom =
                                    (*self.atom_table).intern(@copy name);
                                let subclass = @ids_single(atom, atom);
                                self.build_import_directive(local_module,
                                                            module_path,
                                                            subclass);
                            }
                        }
                        view_path_glob(_, _) {
                            self.build_import_directive(local_module,
                                                        module_path,
                                                        @ids_glob);
                        }
                    }
                }
            }
            view_item_export(*) { /* TODO */ }
            view_item_use(name, _, node_id) {
                alt find_use_stmt_cnum(self.session.cstore, node_id) {
                    some(crate_id) {
                        let atom = (*self.atom_table).intern(@copy name);
                        let child = (*parent_node).add_child(parent_node,
                                                             atom);
                        let def_id = { crate: crate_id, node: 0 };
                        let external_module =
                            (*child).define_external_module(child,
                                                            some(def_id));
                        self.build_reduced_graph_for_external_crate
                            (external_module);
                    }
                    none {
                        /* Ignore. */
                    }
                }
            }
        }
    }

    #[doc="
        Builds the reduced graph rooted at the 'use' directive for an external
        crate.
    "]
    fn build_reduced_graph_for_external_crate(root: @external_module) {
        for each_path(self.session.cstore, root.def_id.get().crate) {
            |path_entry|
            #debug("(building reduced graph for external crate) found path \
                    entry: %s", path_entry.path_string);

            let mut pieces = split_str(path_entry.path_string, "::");
            let final_ident = pop(pieces);

            // Find the module we need, creating modules along the way if we
            // need to.
            let mut current_module_node = root;
            for pieces.each {
                |ident|

                // Create or reuse a graph node for the child.
                let atom = (*self.atom_table).intern(@copy ident);
                let parent_graph_node = current_module_node.parent_graph_node;
                let child_graph_node =
                    (*parent_graph_node).add_child(parent_graph_node, atom);

                // Define or reuse the module node.
                alt child_graph_node.module_def {
                    md_none {
                        #debug("(building reduced graph for external crate) \
                                autovivifying %s", ident);
                        current_module_node =
                            (*child_graph_node).
                                define_external_module(child_graph_node, none);
                    }
                    md_external_module(_) {
                        current_module_node =
                            (*child_graph_node).get_external_module();
                    }
                    md_local_module(_) {
                        fail "unexpected local module";
                    }
                }
            }

            // Add the new child item.
            let atom = (*self.atom_table).intern(@copy final_ident);
            let parent_graph_node = current_module_node.parent_graph_node;
            let child_graph_node =
                (*parent_graph_node).add_child(parent_graph_node, atom);

            alt path_entry.def_like {
                dl_def(def) {
                    alt def {
                        def_mod(def_id) | def_native_mod(def_id) {
                            alt child_graph_node.module_def {
                                md_none {
                                    #debug("(building reduced graph for \
                                            external crate) building module \
                                            %s", final_ident);
                                    (*child_graph_node).
                                        define_external_module
                                            (child_graph_node, some(def_id));
                                }
                                md_external_module(external_module) {
                                    #debug("(building reduced graph for \
                                            external crate) filling in def id \
                                            for %s",
                                            final_ident);
                                    external_module.def_id = some(def_id);
                                }
                                md_local_module(_) {
                                    fail "unexpected local module";
                                }
                            }
                        }
                        def_fn(def_id, _) | def_const(def_id) |
                        def_variant(_, def_id) {
                            #debug("(building reduced graph for external \
                                    crate) building value %s", final_ident);
                            (*child_graph_node).define_value(def);
                        }
                        def_ty(def_id) {
                            #debug("(building reduced graph for external \
                                    crate) building type %s", final_ident);
                            (*child_graph_node).define_type(def);
                        }
                        def_class(def_id) {
                            #debug("(building reduced graph for external \
                                    crate) building value and type %s",
                                    final_ident);
                            (*child_graph_node).define_value(def);
                            (*child_graph_node).define_type(def);
                        }
                        def_self(*) | def_arg(*) | def_local(*) |
                        def_prim_ty(*) | def_ty_param(*) | def_binding(*) |
                        def_use(*) | def_upvar(*) | def_region(*) {
                            fail #fmt("didn't expect %?", def);
                        }
                    }
                }
                dl_impl(def_id) {
                    #debug("(building reduced graph for external crate) \
                            building impl %s", final_ident);
                    (*child_graph_node).define_impl(def_id);
                }
                dl_field {
                    #debug("(building reduced graph for external crate) \
                            ignoring field %s", final_ident);
                }
            }
        }
    }

    #[doc="Creates and adds an import directive to the given module."]
    fn build_import_directive(local_module: @local_module,
                              module_path: @dvec<atom>,
                              subclass: @import_directive_subclass) {
        let directive = @import_directive(module_path, subclass);
        local_module.imports.push(directive);

        // Bump the reference count on the name. Or, if this is a glob, set
        // the appropriate flag.
        alt *subclass {
            ids_single(target, _) {
                alt local_module.import_resolutions.find(target) {
                    some(resolution) {
                        resolution.outstanding_references += 1u;
                    }
                    none {
                        let resolution = @import_resolution();
                        resolution.outstanding_references = 1u;
                        local_module.import_resolutions.insert(target,
                                                              resolution);
                            
                    }
                }
            }
            ids_glob {
                // Set the glob flag. This tells us that we don't know the
                // module's exports ahead of time.
                local_module.glob_count += 1u;
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

            let module_root = (*self.graph_root).get_local_module();
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
    fn resolve_imports_for_module_subtree(local_module: @local_module) {
        #debug("(resolving imports for module subtree) resolving %s",
               self.graph_node_to_str(local_module.parent_graph_node));
        self.resolve_imports_for_module(local_module);

        for local_module.children.each {
            |_name, child_node|
            alt (*child_node).get_local_module_if_available() {
                none { /* Nothing to do. */ }
                some(child_module_node) {
                    self.resolve_imports_for_module_subtree(child_module_node);
                }
            }
        }
    }

    #[doc="Attempts to resolve imports for the given module only."]
    fn resolve_imports_for_module(local_module: @local_module) {
        if (*local_module).all_imports_resolved() {
            #debug("(resolving imports for module) all imports resolved for \
                   %s",
                   self.graph_node_to_str(local_module.parent_graph_node));
            ret;
        }

        let import_count = local_module.imports.len();
        while local_module.resolved_import_count < import_count {
            let import_index = local_module.resolved_import_count;
            let import_directive = local_module.imports.get_elt(import_index);
            alt self.resolve_import_for_module(local_module,
                                               import_directive) {
                rr_failed {
                    // We presumably emitted an error. Continue.
                    #debug("!!! (resolving imports for module) error: %s",
                           self.graph_node_to_str(local_module.
                                                  parent_graph_node));
                }
                rr_indeterminate {
                    // Bail out. We'll come around next time.
                    break;
                }
                rr_success(()) {
                    // Good. Continue.
                }
            }

            local_module.resolved_import_count += 1u;
        }
    }

    #[doc="
        Attempts to resolve the given import. The return value indicates
        failure if we're certain the name does not exist, indeterminate if we
        don't know whether the name exists at the moment due to other
        currently-unresolved imports, or success if we know the name exists. If
        successful, the resolved bindings are written into the module.
    "]
    fn resolve_import_for_module(local_module: @local_module,
                                 import_directive: @import_directive)
            -> resolve_result<()> {

        let mut resolution_result;
        let module_path = import_directive.module_path;

        #debug("(resolving import for module) resolving import '%s::...' in \
                '%s'",
               *(*self.atom_table).atoms_to_str((*module_path).get()),
               self.graph_node_to_str(local_module.parent_graph_node));

        // One-level renaming imports of the form `import foo = bar;` are
        // handled specially.
        if (*module_path).len() == 0u {
            resolution_result =
                self.resolve_one_level_renaming_import(local_module,
                                                       import_directive);
        } else {
            // First, resolve the module path for the directive, if necessary.
            alt self.resolve_module_path_for_import(local_module,
                                                    module_path) {
                rr_failed {
                    resolution_result = rr_failed;
                }
                rr_indeterminate {
                    resolution_result = rr_indeterminate;
                }
                rr_success(md_local_module(containing_module)) {
                    // Attempt to resolve the import.
                    alt *import_directive.subclass {
                        ids_single(target, source) {
                            resolution_result =
                                self.resolve_single_import(local_module,
                                                           containing_module,
                                                           target,
                                                           source);
                        }
                        ids_glob {
                            resolution_result =
                                self.resolve_glob_import(local_module,
                                                         containing_module);
                        }
                    }
                }
                rr_success(md_external_module(containing_module)) {
                    alt *import_directive.subclass {
                        ids_single(target, source) {
                            resolution_result =
                                self.resolve_single_external_import(
                                    local_module,
                                    containing_module,
                                    target,
                                    source);
                        }
                        ids_glob {
                            resolution_result =
                                self.resolve_glob_external_import(local_module,
                                    containing_module);
                        }
                    }
                }
                rr_success(md_none) {
                    fail "md_none unexpected here";
                }
            }
        }

        // Decrement the count of unresolved imports.
        alt resolution_result {
            rr_success(()) {
                assert self.unresolved_imports >= 1u;
                self.unresolved_imports -= 1u;
            }
            _ { /* Nothing to do here; just return the error. */ }
        }

        // Decrement the count of unresolved globs if necessary. But only if
        // the resolution result is indeterminate -- otherwise we'll stop
        // processing imports here. (See the loop in
        // resolve_imports_for_module.)
        if resolution_result != rr_indeterminate {
            alt *import_directive.subclass {
                ids_glob {
                    assert local_module.glob_count >= 1u;
                    local_module.glob_count -= 1u;
                }
                ids_single(*) { /* Ignore. */ }
            }
        }

        ret resolution_result;
    }

    fn resolve_single_import(local_module: @local_module,
                             containing_module: @local_module,
                             target: atom, source: atom)
            -> resolve_result<()> {

        #debug("(resolving single import) resolving '%s' = '%s::%s' from \
                '%s'",
               *(*self.atom_table).atom_to_str(target),
               self.graph_node_to_str(containing_module.parent_graph_node),
               *(*self.atom_table).atom_to_str(source),
               self.graph_node_to_str(local_module.parent_graph_node));

        // We need to resolve all four namespaces for this to succeed.
        //
        // FIXME: See if there's some way of handling namespaces in a more
        // generic way. We have four of them; it seems worth doing...
        let mut module_result = nsr_unknown;
        let mut value_result = nsr_unknown;
        let mut type_result = nsr_unknown;
        let mut impl_result = nsr_unknown;

        // Search for direct children of the containing module.
        alt containing_module.children.find(source) {
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
                if (*child_graph_node).defined_in_namespace(ns_impl) {
                    impl_result = nsr_bound(child_graph_node);
                }
            }
        }

        // Unless we managed to find a result in all four namespaces
        // (exceedingly unlikely), search imports as well.
        alt (module_result, value_result, type_result, impl_result) {
            (nsr_bound(_), nsr_bound(_), nsr_bound(_), nsr_bound(_)) {
                // Continue.
            }
            _ {
                // If there is an unresolved glob at this point in the
                // containing module, bail out. We don't know enough to be able
                // to resolve this import.
                if containing_module.glob_count > 0u {
                    #debug("(resolving single import) unresolved glob; \
                            bailing out");
                    ret rr_indeterminate;
                }

                // Now search the exported imports within the containing
                // module.
                alt containing_module.import_resolutions.find(source) {
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
                        if impl_result == nsr_unknown {
                            impl_result = nsr_unbound;
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
                        if impl_result == nsr_unknown {
                            impl_result = get_binding(import_resolution,
                                                      ns_impl);
                        }
                    }
                    some(_) {
                        // The import is unresolved. Bail out.
                        #debug("(resolving single import) unresolved import; \
                                bailing out");
                        ret rr_indeterminate;
                    }
                }
            }
        }

        // We've successfully resolved the import. Write the results in.
        assert local_module.import_resolutions.contains_key(target);
        let import_resolution = local_module.import_resolutions.get(target);

        alt module_result {
            nsr_bound(binding) {
                #debug("(resolving single import) found module binding");
                import_resolution.module_target = some(binding);
            }
            nsr_unbound {
                #debug("(resolving single import) didn't find module binding");

                #debug("(resolving single import) dumping containing module:");
                self.dump_local_module(containing_module);
            }
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
        alt impl_result {
            nsr_bound(binding) {
                import_resolution.impl_target = some(binding);
            }
            nsr_unbound { /* Continue. */ }
            nsr_unknown { fail "impl result should be known at this point"; }
        }

        assert import_resolution.outstanding_references >= 1u;
        import_resolution.outstanding_references -= 1u;

        #debug("(resolving single import) successfully resolved import");
        ret rr_success(());
    }

    #[doc="
        Resolves a glob import. Note that this function cannot fail; it either
        succeeds or bails out (as importing * from an empty module or a module
        that exports nothing is valid).
    "]
    fn resolve_glob_import(local_module: @local_module,
                           containing_module: @local_module)
            -> resolve_result<()> {

        // This function works in a highly imperative manner; it eagerly adds
        // everything it can to the list of import resolutions of the module
        // node.

        // We must bail out if the node has unresolved imports of any kind
        // (including globs).
        if !(*containing_module).all_imports_resolved() {
            #debug("(resolving glob import) target module has unresolved \
                    imports; bailing out");
            ret rr_indeterminate;
        }

        assert containing_module.glob_count == 0u;

        // Add all resolved imports from the containing module.
        for containing_module.import_resolutions.each {
            |atom, target_import_resolution|

            #debug("(resolving glob import) writing module resolution \
                    %? into '%s'",
                   target_import_resolution.module_target.is_none(),
                   self.graph_node_to_str(local_module.parent_graph_node));

            // Here we merge two import resolutions.
            alt local_module.import_resolutions.find(atom) {
                none {
                    // Simple: just copy the old import resolution.
                    let new_import_resolution = @import_resolution();
                    new_import_resolution.module_target =
                        target_import_resolution.module_target;
                    new_import_resolution.value_target =
                        target_import_resolution.value_target;
                    new_import_resolution.type_target =
                        target_import_resolution.type_target;
                    new_import_resolution.impl_target =
                        target_import_resolution.impl_target;

                    local_module.import_resolutions.insert(atom,
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
                    alt target_import_resolution.impl_target {
                        none { /* Continue. */ }
                        some(impl_target) {
                            dest_import_resolution.impl_target =
                                some(impl_target);
                        }
                    }
                }
            }
        }

        // Add all children from the containing module.
        for containing_module.children.each {
            |atom, graph_node|

            let mut dest_import_resolution;
            alt local_module.import_resolutions.find(atom) {
                none {
                    // Create a new import resolution from this child.
                    dest_import_resolution = @import_resolution();
                    local_module.import_resolutions.insert(atom,
                            dest_import_resolution);
                }
                some(existing_import_resolution) {
                    dest_import_resolution = existing_import_resolution;
                }
            }


            #error("(resolving glob import) writing module resolution \
                    '%s'",
                   self.graph_node_to_str(local_module.parent_graph_node));

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
            if (*graph_node).defined_in_namespace(ns_impl) {
                dest_import_resolution.impl_target = some(graph_node);
            }
        }

        #debug("(resolving glob import) successfully resolved import");
        ret rr_success(());
    }

    // FIXME: This duplicates code from resolve_single_import.
    fn resolve_single_external_import(local_module: @local_module,
                                      containing_module: @external_module,
                                      target: atom, source: atom)
            -> resolve_result<()> {

        #debug("(resolving single external import) resolving import '%s' = \
                '%s::%s' in '%s'",
               *(*self.atom_table).atom_to_str(target),
               self.graph_node_to_str(containing_module.parent_graph_node),
               *(*self.atom_table).atom_to_str(source),
               self.graph_node_to_str(local_module.parent_graph_node));

        // We need to resolve all four namespaces for this to succeed.
        let mut module_result = none;
        let mut value_result = none;
        let mut type_result = none;
        let mut impl_result = none;

        // Search for direct children of the containing module.
        alt containing_module.children.find(source) {
            none { /* Continue. */ }
            some(child_graph_node) {
                if (*child_graph_node).defined_in_namespace(ns_module) {
                    module_result = some(child_graph_node);
                }
                if (*child_graph_node).defined_in_namespace(ns_value) {
                    value_result = some(child_graph_node);
                }
                if (*child_graph_node).defined_in_namespace(ns_type) {
                    type_result = some(child_graph_node);
                }
                if (*child_graph_node).defined_in_namespace(ns_impl) {
                    impl_result = some(child_graph_node);
                }
            }
        }

        // If no namespaces were resolved, that's an error.
        if module_result.is_none() && value_result.is_none() &&
                type_result.is_none() && impl_result.is_none() {
            #debug("!!! (resolving single external import) failed");
            ret rr_failed;
        }

        // We've successfully resolved the import. Write the results in.
        assert local_module.import_resolutions.contains_key(target);
        let import_resolution = local_module.import_resolutions.get(target);

        alt module_result {
            none { /* Continue. */ }
            some(binding) {
                #error("(resolving glob import) writing module resolution \
                        '%s'",
                       self.graph_node_to_str(local_module.parent_graph_node));

                import_resolution.module_target = some(binding);
            }
        }
        alt value_result {
            none { /* Continue. */ }
            some(binding) {
                import_resolution.value_target = some(binding);
            }
        }
        alt type_result {
            none { /* Continue. */ }
            some(binding) {
                import_resolution.type_target = some(binding);
            }
        }
        alt impl_result {
            none { /* Continue. */ }
            some(binding) {
                import_resolution.impl_target = some(binding);
            }
        }

        assert import_resolution.outstanding_references >= 1u;
        import_resolution.outstanding_references -= 1u;

        #debug("(resolving external import) success");
        ret rr_success(());
    }

    // FIXME: This duplicates code from resolve_glob_import.
    fn resolve_glob_external_import(local_module: @local_module,
                                    containing_module: @external_module)
            -> resolve_result<()> {

        #debug("(resolving glob external import) resolving");

        // Add all children from the containing module.
        for containing_module.children.each {
            |atom, graph_node|

            let mut dest_import_resolution;
            alt local_module.import_resolutions.find(atom) {
                none {
                    // Create a new import resolution from this child.
                    dest_import_resolution = @import_resolution();
                    local_module.import_resolutions.insert(atom,
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
            if (*graph_node).defined_in_namespace(ns_impl) {
                dest_import_resolution.impl_target = some(graph_node);
            }
        }

        #debug("(resolving external glob import) success");
        ret rr_success(());
    }

    #[doc="
        Attempts to resolve the module part of an import directive rooted at
        the given module.
    "]
    fn resolve_module_path_for_import(local_module: @local_module,
                                      module_path: @dvec<atom>)
            -> resolve_result<module_def> {

        let module_path_len = (*module_path).len();
        assert module_path_len > 0u;

        #debug("(resolving module path for import) processing '%s' rooted at \
               '%s'",
               *(*self.atom_table).atoms_to_str((*module_path).get()),
               self.graph_node_to_str(local_module.parent_graph_node));

        // The first element of the module path must be in the current scope
        // chain.
        let first_element = (*module_path).get_elt(0u);
        let mut search_module_def;
        alt self.resolve_module_in_lexical_scope(local_module, first_element) {
            rr_failed {
                #error("(resolving module path for import) !!! unresolved \
                        name: %s",
                       *(*self.atom_table).atom_to_str(first_element));

                self.dump_local_module(local_module);

                ret rr_failed;
            }
            rr_indeterminate {
                #debug("(resolving module path for import) indeterminate; \
                        bailing");
                ret rr_indeterminate;
            }
            rr_success(resulting_module_def) {
                search_module_def = resulting_module_def;
            }
        }

        // Now resolve the rest of the path. This does not involve looking
        // upward though scope chains; we simply resolve names directly in
        // modules as we go.
        let mut index = 1u;
        while index < module_path_len {
            let name = (*module_path).get_elt(index);
            alt self.resolve_name_in_module(search_module_def, name,
                                            ns_module) {
                rr_failed {
                    #debug("!!! (resolving module path for import) module \
                           resolution failed: %s",
                           *(*self.atom_table).atom_to_str(name));
                    ret rr_failed;
                }
                rr_indeterminate {
                    #debug("(resolving module path for import) module \
                           resolution is indeterminate: %s",
                           *(*self.atom_table).atom_to_str(name));
                    ret rr_indeterminate;
                }
                rr_success(graph_node) {
                    alt graph_node.module_def {
                        md_none {
                            // Not a module.
                            #debug("!!! (resolving module path for import) \
                                   not a module: %s",
                                   *(*self.atom_table).atom_to_str(name));
                            ret rr_failed;
                        }
                        md_local_module(*) | md_external_module(*) {
                            search_module_def = graph_node.module_def;
                        }
                    }
                }
            }

            index += 1u;
        }

        #debug("(resolving module path for import) resolved module");
        ret rr_success(search_module_def);
    }

    fn resolve_item_in_lexical_scope(local_module: @local_module, name: atom,
                                     namespace: namespace)
            -> resolve_result<@graph_node> {

        #debug("(resolving item in lexical scope) resolving '%s' in namespace \
                %? in '%s'",
               *(*self.atom_table).atom_to_str(name),
               namespace,
               self.graph_node_to_str(local_module.parent_graph_node));

        // The current module node is handled specially. First, check for
        // its immediate children.
        alt local_module.children.find(name) {
            some(graph_node) if (*graph_node).defined_in_namespace(namespace) {
                ret rr_success(graph_node);
            }
            some(_) | none { /* Not found; continue. */ }
        }

        // Now check for its import directives. We don't have to have resolved
        // all its imports in the usual way; this is because chains of adjacent
        // import statements are processed as though they mutated the current
        // scope.
        alt local_module.import_resolutions.find(name) {
            none { /* Not found; continue. */ }
            some(import_resolution) {
                alt (*import_resolution).target_for_namespace(namespace) {
                    none {
                        /* Not found; continue. */
                        #debug("(resolving item in lexical scope) found \
                                import resolution, but not in namespace %?",
                               namespace);
                    }
                    some(target_graph_node) {
                        ret rr_success(target_graph_node);
                    }
                }
            }
        }
        
        // Finally, proceed up the scope chain looking for parent modules.
        let mut search_module = local_module;
        loop {
            // Go to the next parent.
            alt search_module.parent_graph_node.parent_node {
                none {
                    // No more parents. This module was unresolved.
                    #debug("(resolving item in lexical scope) unresolved \
                            module");
                    ret rr_failed;
                }
                some(gnh_graph_node(parent_node)) {
                    alt (*parent_node).get_local_module_if_available() {
                        none {
                            // The parent is not a module. This should not
                            // happen.
                            #error("!!! (resolving item in lexical scope) \
                                    UNEXPECTED: parent is not a module");
                            ret rr_failed;
                        }
                        some(parent_module_node) {
                            search_module = parent_module_node;
                        }
                    }
                }
            }

            // Resolve the name in the parent module.
            alt self.resolve_name_in_local_module(search_module, name,
                                                  namespace) {
                rr_failed {
                    // Continue up the search chain.
                }
                rr_indeterminate {
                    // We couldn't see through the higher scope because of an
                    // unresolved import higher up. Bail.
                    #debug("(resolving item in lexical scope) indeterminate \
                            higher scope; bailing");
                    ret rr_indeterminate;
                }
                rr_success(graph_node) {
                    // We found the module.
                    ret rr_success(graph_node);
                }
            }
        }
    }

    fn resolve_module_in_lexical_scope(local_module: @local_module, name: atom)
            -> resolve_result<module_def> {

        alt self.resolve_item_in_lexical_scope(local_module, name, ns_module) {
            rr_success(graph_node) {
                alt graph_node.module_def {
                    md_none {
                        #error("!!! (resolving module in lexical scope) module
                                wasn't actually a module!");
                        ret rr_failed;
                    }
                    md_local_module(*) | md_external_module(*) {
                        ret rr_success(graph_node.module_def);
                    }
                }
            }
            rr_indeterminate {
                #debug("(resolving module in lexical scope) indeterminate; \
                        bailing");
                ret rr_indeterminate;
            }
            rr_failed {
                #debug("(resolving module in lexical scope) failed to \
                        resolve");
                ret rr_failed;
            }
        }
    }

    #[doc="
        Attempts to resolve the supplied name in the given module for the
        given namespace. If successful, returns the reduced graph node
        corresponding to the name.
    "]
    fn resolve_name_in_module(module_def: module_def, name: atom,
                              namespace: namespace)
            -> resolve_result<@graph_node> {

        alt module_def {
            md_none { fail "(resolving name in module) unexpected md_none"; }
            md_local_module(local_module) {
                ret self.resolve_name_in_local_module(local_module, name,
                                                      namespace);
            }
            md_external_module(external_module) {
                ret self.resolve_name_in_external_module(external_module,
                                                         name, namespace);
            }
        }
    }

    fn resolve_name_in_local_module(local_module: @local_module, name: atom,
                                    namespace: namespace)
            -> resolve_result<@graph_node> {

        #debug("(resolving name in local module) resolving '%s' in '%s'",
               *(*self.atom_table).atom_to_str(name),
               self.graph_node_to_str(local_module.parent_graph_node));

        // First, check the direct children of the module.
        alt local_module.children.find(name) {
            some(child_node) if (*child_node).defined_in_namespace(namespace) {
                #debug("(resolving name in local module) found node as child");
                ret rr_success(child_node);
            }
            some(_) | none {
                // Continue.
            }
        }

        // Next, check the module's imports. If the module has a glob, then
        // we bail out; we don't know its imports.
        if local_module.glob_count > 0u {
            #debug("(resolving name in local module) module has glob; bailing \
                    out");
            ret rr_indeterminate;
        }

        // Otherwise, we check the list of resolved imports.
        alt local_module.import_resolutions.find(name) {
            some(import_resolution) {
                if import_resolution.outstanding_references != 0u {
                    #debug("(resolving name in local module) import \
                            unresolved; bailing out");
                    ret rr_indeterminate;
                }

                alt (*import_resolution).target_for_namespace(namespace) {
                    none { /* Continue. */ }
                    some(target) {
                        #debug("(resolving name in local module) resolved to \
                                import");
                        ret rr_success(target);
                    }
                }
            }
            none {
                // Continue.
            }
        }

        // We're out of luck.
        #debug("(resolving name in local module) failed to resolve %s",
               *(*self.atom_table).atom_to_str(name));
        ret rr_failed;
    }

    #[doc="
        Resolves a one-level renaming import of the kind `import foo = bar;`
        This needs special handling, as, unlike all of the other imports, it
        needs to look in the scope chain for modules and non-modules alike.
    "]
    fn resolve_one_level_renaming_import(local_module: @local_module,
                                         import_directive: @import_directive)
            -> resolve_result<()> {

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
                '%s' in '%s'",
                *(*self.atom_table).atom_to_str(target_name),
                *(*self.atom_table).atom_to_str(source_name),
                self.graph_node_to_str(local_module.parent_graph_node));

        // Find the matching items in the lexical scope chain for every
        // namespace. If any of them come back indeterminate, this entire
        // import is indeterminate.
        let mut module_result;
        #debug("(resolving one-level naming result) searching for module");
        alt self.resolve_item_in_lexical_scope(local_module, source_name,
                                               ns_module) {
            rr_failed {
                #debug("(resolving one-level renaming import) didn't find \
                        module result");
                module_result = none;
            }
            rr_indeterminate {
                #debug("(resolving one-level renaming import) module result \
                        is indeterminate; bailing");
                ret rr_indeterminate;
            }
            rr_success(graph_node) {
                #debug("(resolving one-level renaming import) module result \
                        found");
                module_result = some(graph_node);
            }
        }

        let mut value_result;
        #debug("(resolving one-level naming result) searching for value");
        alt self.resolve_item_in_lexical_scope(local_module, source_name,
                                               ns_value) {
            rr_failed {
                #debug("(resolving one-level renaming import) didn't find \
                        value result");
                value_result = none;
            }
            rr_indeterminate {
                #debug("(resolving one-level renaming import) value result is \
                        indeterminate; bailing");
                ret rr_indeterminate;
            }
            rr_success(graph_node) {
                #debug("(resolving one-level renaming import) value result \
                        found");
                value_result = some(graph_node);
            }
        }

        let mut type_result;
        #debug("(resolving one-level naming result) searching for type");
        alt self.resolve_item_in_lexical_scope(local_module, source_name,
                                               ns_type) {
            rr_failed {
                #debug("(resolving one-level renaming import) didn't find \
                        type result");
                type_result = none;
            }
            rr_indeterminate {
                #debug("(resolving one-level renaming import) type result is \
                        indeterminate; bailing");
                ret rr_indeterminate;
            }
            rr_success(graph_node) {
                #debug("(resolving one-level renaming import) type result \
                        found");
                type_result = some(graph_node);
            }
        }

        //
        // NB: This one results in effects that may be somewhat surprising. It
        // means that this:
        //
        // mod A {
        //     impl foo for ... { ... }
        //     mod B {
        //         impl foo for ... { ... }
        //         import bar = foo;
        //         ...
        //     }
        // }
        //
        // results in only A::B::foo being aliased to A::B::bar, not A::foo
        // *and* A::B::foo being aliased to A::B::bar.
        //

        let mut impl_result;
        #debug("(resolving one-level naming result) searching for impl");
        alt self.resolve_item_in_lexical_scope(local_module, source_name,
                                               ns_impl) {
            rr_failed {
                #debug("(resolving one-level renaming import) didn't find \
                        impl result");
                impl_result = none;
            }
            rr_indeterminate {
                #debug("(resolving one-level renaming import) impl result is \
                        indeterminate; bailing");
                ret rr_indeterminate;
            }
            rr_success(graph_node) {
                #debug("(resolving one-level renaming import) impl result \
                        found");
                impl_result = some(graph_node);
            }
        }

        // If nothing at all was found, that's an error.
        if module_result.is_none() && value_result.is_none() &&
                type_result.is_none() && impl_result.is_none() {
            #error("!!! (resolving one-level renaming import) couldn't find \
                    anything with that name");
            ret rr_failed;
        }

        // Otherwise, proceed and write in the bindings.
        alt local_module.import_resolutions.find(target_name) {
            none {
                fail "(resolving one-level renaming import) reduced graph \
                      construction or glob importing should have created the \
                      import resolution name by now";
            }
            some(import_resolution) {
                #error("(resolving one-level renaming import) writing module \
                        result %? for '%s' into '%s'",
                       module_result.is_none(),
                       *(*self.atom_table).atom_to_str(target_name),
                       self.graph_node_to_str(local_module.parent_graph_node));

                import_resolution.module_target = module_result;
                import_resolution.value_target = value_result;
                import_resolution.type_target = type_result;
                import_resolution.impl_target = impl_result;

                assert import_resolution.outstanding_references >= 1u;
                import_resolution.outstanding_references -= 1u;
            }
        }

        #debug("(resolving one-level renaming import) successfully resolved");
        ret rr_success(());
    }

    fn resolve_name_in_external_module(parent_module: @external_module,
                                       name: atom, namespace: namespace)
            -> resolve_result<@graph_node> {
        #debug("(resolving name in external module) resolving '%s' in \
                external",
                *(*self.atom_table).atom_to_str(name));

        alt parent_module.children.find(name) {
            some(child_node) if (*child_node).defined_in_namespace(namespace) {
                // The node is a direct child.
                #debug("(resolving name in external module) found node as \
                        child");
                ret rr_success(child_node);
            }
            some(_) | none {
                // We're out of luck.
                #debug("(resolving name in external module) failed");
                ret rr_failed;
            }
        }
    }

    fn report_unresolved_imports(graph_node: @graph_node) {
        let mut local_module;
        alt (*graph_node).get_local_module_if_available() {
            none { ret; }
            some(associated_module_node) {
                local_module = associated_module_node;
            }
        }

        let index = local_module.resolved_import_count;
        let import_count = local_module.imports.len();
        if index != import_count {
            let module_path = local_module.imports.get_elt(index).module_path;
            #error("!!! unresolved import in %s: %s",
                   self.graph_node_to_str(local_module.parent_graph_node),
                   *(*self.atom_table).atoms_to_str((*module_path).get()));
        }

        // Descend into children.
        for local_module.children.each {
            |_name, child_node|
            self.report_unresolved_imports(child_node);
        }
    }

    //
    // AST resolution
    //
    // We proceed by building up a list of scopes. Each scope is simply an
    // integer key. We associate identifiers with their namespaces and scopes
    // in one large hash table.
    //

    fn with_scope(name: option<atom>, f: fn()) {
        let orig_graph_node = self.current_graph_node;

        // Create a new scope ID.
        (*self.scopes).push(self.next_scope_id);
        self.next_scope_id += 1u;

        // Move down in the graph.
        alt name {
            none { /* Nothing to do. */ }
            some(name) {
                alt (*orig_graph_node).get_local_module_if_available() {
                    none {
                        #debug("!!! (with scope) no local module");
                    }
                    some(local_module) {
                        alt local_module.children.find(name) {
                            none {
                                #debug("!!! (with scope) no child found");
                            }
                            some(child_node) {
                                self.current_graph_node = child_node;
                                self.populate_scope(local_module);
                            }
                        }
                    }
                }
            }
        }

        f();

        (*self.scopes).pop();
        self.current_graph_node = orig_graph_node;
    }

    fn populate_scope(local_module: @local_module) {
        // First, populate the scope with imports. (Since children override
        // imports, we must do this first.)
        for local_module.import_resolutions.each {
            |atom, import_resolution|

            self.maybe_bind_import_resolution(atom, import_resolution,
                                              ns_module);
            self.maybe_bind_import_resolution(atom, import_resolution,
                                              ns_type);
            self.maybe_bind_import_resolution(atom, import_resolution,
                                              ns_value);
            self.maybe_bind_import_resolution(atom, import_resolution,
                                              ns_impl);
        }

        // TODO
    }

    fn maybe_bind_import_resolution(atom: atom,
                                    import_resolution: @import_resolution,
                                    namespace: namespace) {
        alt (*import_resolution).target_for_namespace(namespace) {
            none {
                // Nothing to do.
            }
            some(target_graph_node) {
                alt namespace {
                    ns_module {
                        if (*target_graph_node).
                                defined_in_namespace(ns_module) {
                            self.add_binding(atom, namespace,
                                             dl_def(def_mod({
                                                crate: 0,
                                                node: 0
                                             })));
                        }
                    }
                    ns_type {
                        alt target_graph_node.type_def {
                            none { /* Nothing to do. */ }
                            some(def) {
                                self.add_binding(atom, namespace, dl_def(def));
                            }
                        }
                    }
                    ns_value {
                        alt target_graph_node.value_def {
                            none { /* Nothing to do. */ }
                            some(def) {
                                self.add_binding(atom, namespace, dl_def(def));
                            }
                        }
                    }
                    ns_impl {
                        for target_graph_node.impl_defs.each {
                            |def_id|
                            self.add_binding(atom, namespace, dl_impl(def_id));
                        }
                    }
                }
            }
        }
    }

    fn add_binding(name: atom, namespace: namespace, def_like: def_like) {
        let mut these_name_bindings;
        alt self.names.find(name) {
            none {
                these_name_bindings = @name_bindings();
                self.names.insert(name, these_name_bindings);
            }
            some(existing_name_bindings) {
                these_name_bindings = existing_name_bindings;
            }
        }

        let new_binding = @name_binding((*self.scopes).last(), def_like);
        alt namespace {
            ns_module {
                (*these_name_bindings.module_bindings).push(new_binding);
            }
            ns_type {
                (*these_name_bindings.type_bindings).push(new_binding);
            }
            ns_value {
                (*these_name_bindings.value_bindings).push(new_binding);
            }
            ns_impl {
                (*these_name_bindings.impl_bindings).push(new_binding);
            }
        }
    }

    fn resolve_crate() unsafe {
        // FIXME: This is awful!
        let this = ptr::addr_of(self);
        visit_crate(*self.crate, (), mk_vt(@{
            visit_item: {
                |item, _context, visitor|
                (*this).resolve_item(item, visitor);
            },
            visit_arm: {
                |arm, _context, visitor|
                (*this).resolve_arm(arm, visitor);
            },
            visit_block: {
                |block, _context, visitor|
                (*this).resolve_block(block, visitor);
            }
            with *default_visitor()
        }));
    }

    fn resolve_item(item: @item, visitor: resolve_visitor) {
        let atom = (*self.atom_table).intern(@copy item.ident);
        self.with_scope(some(atom)) {
            ||

            alt item.node {
                item_enum(*) | item_ty(*) {
                    visit_item(item, (), visitor);
                }
                item_impl(_, _, _, _, methods) {
                    // Create a new scope for the impl-wide type parameters.
                    for methods.each {
                        |method|
                        // We also need a new scope for the method-specific
                        // type parameters.
                        visit_fn(fk_method(method.ident, method.tps, method),
                                 method.decl, method.body, method.span,
                                 method.id,
                                 (), visitor);
                    }
                }
                item_iface(_, _, methods) {
                    // Create a new scope for the interface-wide type parameters.
                    for methods.each {
                        |method|
                        // We also need a new scope for the method-specific type
                        // parameters.
                        visit_ty(method.decl.output, (), visitor);
                    }
                }
                item_class(*) {
                    // Create a new scope for the class-wide type parameters.
                    // FIXME: Handle methods properly.
                    visit_item(item, (), visitor);
                }
                item_mod(module) {
                    self.resolve_module(module, item.span, item.ident, item.id,
                                        visitor);
                }
                item_native_mod(native_module) {
                    for native_module.items.each {
                        |native_item|
                        alt native_item.node {
                            native_item_fn(*) {
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
    }

    fn resolve_module(module: _mod, span: span, name: ident, id: node_id,
                      visitor: resolve_visitor) {
        self.add_binding((*self.atom_table).intern(@copy name), ns_module,
                         dl_def(def_mod({ crate: 0, node: id })));

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

                    let atom =
                        (*self.atom_table).intern(@copy path.idents[0]);
                    self.add_binding(atom, ns_value,
                                     dl_def(def_local(pattern.id, false)));
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

    #[doc="
        A terribly inefficient routine to print out the name of a graph node.
    "]
    fn graph_node_to_str(graph_node: @graph_node) -> str {
        let atoms = dvec();
        let mut current_node = graph_node;
        loop {
            alt current_node.parent_node {
                none { break; }
                some(gnh_graph_node(parent_node)) {
                    alt parent_node.module_def {
                        md_none { break; }
                        md_local_module(local_module) {
                            for local_module.children.each {
                                |name, child_node|
                                if box::ptr_eq(child_node, graph_node) {
                                    atoms.push(name);
                                    break;
                                }
                            }

                            current_node = local_module.parent_graph_node;
                        }
                        md_external_module(external_module) {
                            for external_module.children.each {
                                |name, child_node|
                                if box::ptr_eq(child_node, graph_node) {
                                    atoms.push(name);
                                    break;
                                }
                            }

                            current_node = external_module.parent_graph_node;
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
            string += *(*self.atom_table).atom_to_str(atoms.get_elt(i));

            if i == 0u {
                break;
            }
            i -= 1u;
        }

        ret string;
    }

    fn dump_local_module(local_module: @local_module) {
        #debug("Dump of module '%s':",
               self.graph_node_to_str(local_module.parent_graph_node));

        #debug("Children:");
        for local_module.children.each {
            |name, _child|

            #debug("* %s", *(*self.atom_table).atom_to_str(name));
        }

        #debug("Import resolutions:");
        for local_module.import_resolutions.each {
            |name, import_resolution|

            let mut module_repr;
            alt (*import_resolution).target_for_namespace(ns_module) {
                none { module_repr = ""; }
                some(target) {
                    module_repr = " module:" + self.graph_node_to_str(target);
                }
            }

            let mut value_repr;
            alt (*import_resolution).target_for_namespace(ns_value) {
                none { value_repr = ""; }
                some(target) {
                    value_repr = " value:" + self.graph_node_to_str(target);
                }
            }

            let mut type_repr;
            alt (*import_resolution).target_for_namespace(ns_type) {
                none { type_repr = ""; }
                some(target) {
                    type_repr = " type:" + self.graph_node_to_str(target);
                }
            }

            let mut impl_repr;
            alt (*import_resolution).target_for_namespace(ns_impl) {
                none { impl_repr = ""; }
                some(target) {
                    impl_repr = " impl:" + self.graph_node_to_str(target);
                }
            }

            #debug("* %s:%s%s%s%s",
                   *(*self.atom_table).atom_to_str(name),
                   module_repr, value_repr, type_repr, impl_repr);
        }
    }
}

#[doc="Entry point to crate resolution."]
fn resolve_crate(session: session, ast_map: ast_map_t, crate: @crate)
        -> { def_map: def_map, impl_map: impl_map } {
    let resolver = @resolver(session, ast_map, crate);
    (*resolver).resolve(resolver);
    ret { def_map: resolver.def_map, impl_map: resolver.impl_map };
}

