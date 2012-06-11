import driver::session::session;
import metadata::csearch::{each_path, lookup_defs};
import metadata::cstore::find_use_stmt_cnum;
import metadata::decoder::{def_like, dl_def, dl_field, dl_impl};
import syntax::ast::{_mod, arm, blk, crate, crate_num, def, def_arg};
import syntax::ast::{def_binding, def_class, def_const, def_fn, def_id};
import syntax::ast::{def_local, def_mod, def_native_mod, def_prim_ty};
import syntax::ast::{def_region, def_self, def_ty, def_ty_param, def_upvar};
import syntax::ast::{def_use, def_variant, expr, expr_fn, expr_fn_block};
import syntax::ast::{expr_path, fn_decl, ident, item, item_class, item_const};
import syntax::ast::{item_enum, item_fn, item_iface, item_impl, item_mod};
import syntax::ast::{item_native_mod, item_res, item_ty, local};
import syntax::ast::{native_item_fn, node_id, pat, pat_ident, ty_param};
import syntax::ast::{variant, view_item, view_item_export, view_item_import};
import syntax::ast::{view_item_use, view_path_glob, view_path_list};
import syntax::ast::{view_path_simple};
import syntax::ast_util::{local_def, walk_pat};
import syntax::codemap::span;
import syntax::visit::{default_visitor, fk_method, mk_vt, visit_block};
import syntax::visit::{visit_crate, visit_expr, visit_expr_opt, visit_fn};
import syntax::visit::{visit_item, visit_mod, visit_native_item, visit_ty};
import syntax::visit::{vt};
import dvec::{dvec, extensions};
import std::list::list;
import std::map::{hashmap, int_hash, str_hash};
import str::split_str;
import vec::pop;
import ASTMap = syntax::ast_map::map;

type DefMap = hashmap<node_id, def>;

// Implementation resolution stuff
type MethodInfo = { did: def_id, n_tps: uint, ident: ident };
type Impl = { did: def_id, ident: ident, methods: [@MethodInfo] };
type ImplScope = @[@Impl];
type ImplScopes = @list<ImplScope>;
type ImplMap = hashmap<node_id, ImplScopes>;

enum PatternBindingMode {
    RefutableMode,
    IrrefutableMode
}

enum Namespace {
    ModuleNamespace,
    TypeNamespace,
    ValueNamespace,
    ImplNamespace
}

enum TargetModule {
    LocalTargetModule(@LocalModule),
    ExternalTargetModule(@ExternalModule)
}

enum NamespaceResult {
    UnknownResult,
    UnboundResult,
    BoundResult(TargetModule, @NameBindings)
}

enum Mutability {
    Mutable,
    Immutable
}

enum SelfBinding {
    HasSelfBinding(node_id),
    NoSelfBinding
}

type ResolveVisitor = vt<()>;

enum ModuleDef {
    NoModuleDef,                            // Does not define a module.
    LocalModuleDef(@LocalModule),           // Defines a local module.
    ExternalModuleDef(@ExternalModule)      // Defines an external module.
}

#[doc="Contains data for specific types of import directives."]
enum ImportDirectiveSubclass {
    SingleImport(Atom /* target */, Atom /* source */),
    GlobImport
}

#[doc="The context that we thread through while building the reduced graph."]
enum ReducedGraphParent {
    LocalModuleParent(@LocalModule),
    ExternalModuleParent(@ExternalModule),
    BlockParent(@LocalModule, node_id)
}

enum ResolveResult<T> {
    Failed,         // Failed to resolve the name.
    Indeterminate,  // Couldn't determine due to unresolved globs.
    Success(T)      // Successfully resolved the import.
}

// FIXME (issue 2550): Should be a class but then it becomes not implicitly
// copyable due to a kind bug.
type Atom = uint;

fn Atom(n: uint) -> Atom {
    ret n;
}

class AtomTable {
    let atoms: hashmap<@str,Atom>;
    let strings: dvec<@str>;
    let mut atom_count: uint;

    new() {
        self.atoms = hashmap::<@str,Atom>({ |x| str::hash(*x) },
                                          { |x, y| str::eq(*x, *y) });
        self.strings = dvec();
        self.atom_count = 0u;
    }

    fn intern(string: @str) -> Atom {
        alt self.atoms.find(string) {
            none { /* fall through */ }
            some(atom) { ret atom; }
        }

        let atom = Atom(self.atom_count);
        self.atom_count += 1u;
        self.atoms.insert(string, atom);
        self.strings.push(string);

        ret atom;
    }

    fn atom_to_str(atom: Atom) -> @str {
        ret self.strings.get_elt(atom);
    }

    fn atoms_to_strs(atoms: [Atom], f: fn(@str) -> bool) {
        for atoms.each {
            |atom|
            if !f(self.atom_to_str(atom)) {
                ret;
            }
        }
    }

    fn atoms_to_str(atoms: [Atom]) -> @str {
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

#[doc="Creates a hash table of atoms."]
fn atom_hashmap<V:copy>() -> hashmap<Atom,V> {
    ret hashmap::<Atom,V>({ |a| a }, { |a, b| a == b });
}

#[doc="
    One local scope. In Rust, local scopes can only contain value bindings.
    Therefore, we don't have to worry about the other namespaces here.
"]
class Rib {
    let bindings: hashmap<Atom,def_like>;

    new() {
        self.bindings = atom_hashmap();
    }
}

#[doc="One import directive."]
class ImportDirective {
    let module_path: @dvec<Atom>;
    let subclass: @ImportDirectiveSubclass;

    new(module_path: @dvec<Atom>, subclass: @ImportDirectiveSubclass) {
        self.module_path = module_path;
        self.subclass = subclass;
    }
}

#[doc="The item that an import resolves to."]
class ImportResolutionTarget {
    let target_module: TargetModule;
    let bindings: @NameBindings;

    new(target_module: TargetModule,
        bindings: @NameBindings) {

        self.target_module = target_module;
        self.bindings = bindings;
    }
}

class ImportResolution {
    // The number of outstanding references to this name. When this reaches
    // zero, outside modules can count on the targets being correct. Before
    // then, all bets are off; future imports could override this name.
    let mut outstanding_references: uint;

    let mut module_target: option<ImportResolutionTarget>;
    let mut value_target: option<ImportResolutionTarget>;
    let mut type_target: option<ImportResolutionTarget>;
    let mut impl_target: option<ImportResolutionTarget>;

    new() {
        self.outstanding_references = 0u;

        self.module_target = none;
        self.value_target = none;
        self.type_target = none;
        self.impl_target = none;
    }

    fn target_for_namespace(namespace: Namespace)
            -> option<ImportResolutionTarget> {
        alt namespace {
            ModuleNamespace { ret copy self.module_target; }
            TypeNamespace   { ret copy self.type_target;   }
            ValueNamespace  { ret copy self.value_target;  }
            ImplNamespace   { ret copy self.impl_target;   }
        }
    }
}

#[doc="The link from a local module up to its nearest parent node."]
enum LocalParentLink {
    NoParentLink,
    LocalModuleParentLink(@LocalModule, Atom),
    BlockParentLink(@LocalModule, node_id)
}

#[doc="One node in the tree of modules."]
class LocalModule {
    let parent_link: LocalParentLink;

    let children: hashmap<Atom,@NameBindings>;
    let imports: dvec<@ImportDirective>;

    //
    // The anonymous children of this node. Anonymous children are pseudo-
    // modules that are implicitly created around items contained within
    // blocks.
    //
    // For example, if we have this:
    //
    //  fn f() {
    //      fn g() {
    //          ...
    //      }
    //  }
    //
    // There will be an anonymous module created around `g` with the ID of the
    // entry block for `f`.
    //

    let anonymous_children: hashmap<node_id,@LocalModule>;

    // The status of resolving each import in this module.
    let import_resolutions: hashmap<Atom,@ImportResolution>;

    // The number of unresolved globs that this module exports.
    let mut glob_count: uint;

    // The index of the import we're resolving.
    let mut resolved_import_count: uint;

    new(parent_link: LocalParentLink) {
        self.parent_link = parent_link;

        self.children = atom_hashmap();
        self.imports = dvec();

        self.anonymous_children = int_hash();

        self.import_resolutions = atom_hashmap();
        self.glob_count = 0u;
        self.resolved_import_count = 0u;
    }

    fn all_imports_resolved() -> bool {
        ret self.imports.len() == self.resolved_import_count;
    }
}

#[doc="The link from a local module up to its nearest parent node."]
enum ExternalParentLink {
    LocalExternalParentLink(@LocalModule, Atom),
    ExternalExternalParentLink(@ExternalModule, Atom)
}

#[doc="An external module in the graph."]
class ExternalModule {
    let parent_link: ExternalParentLink;
    let mut def_id: option<def_id>;

    let children: hashmap<Atom,@NameBindings>;

    new(parent_link: ExternalParentLink, def_id: option<def_id>) {
        self.parent_link = parent_link;
        self.def_id = def_id;

        self.children = atom_hashmap();
    }
}

// FIXME: This is a workaround due to is_none in the standard library
// mistakenly requiring a T:copy.
fn is_none<T>(x: option<T>) -> bool {
    alt x {
        none { ret true; }
        some(_) { ret false; }
    }
}

#[doc="
    Records the definitions (at most one for each namespace) that a name is
    bound to.
"]
class NameBindings {
    let mut module_def: ModuleDef;      // Meaning in the module namespace.
    let mut type_def: option<def>;      // Meaning in the type namespace.
    let mut value_def: option<def>;     // Meaning in the value namespace.
    let mut impl_defs: [def_id];        // Meaning in the impl namespace.

    new() {
        self.module_def = NoModuleDef;
        self.type_def = none;
        self.value_def = none;
        self.impl_defs = [];
    }

    #[doc="Creates a new local module in this set of name bindings."]
    fn define_local_module(parent_link: LocalParentLink) {
        if self.module_def == NoModuleDef {
            self.module_def = LocalModuleDef(@LocalModule(parent_link));
        }
    }

    #[doc="
        Creates a new external module with the given crate ID in this set of
        name bindings.
    "]
    fn define_external_module(parent_link: ExternalParentLink,
                              def_id: option<def_id>)
                           -> @ExternalModule {

        assert self.module_def == NoModuleDef;  // FIXME: should be an error
        let external_module = @ExternalModule(parent_link, def_id);
        self.module_def = ExternalModuleDef(external_module);
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
    fn get_local_module_if_available() -> option<@LocalModule> {
        alt self.module_def {
            NoModuleDef                     { ret none;               }
            LocalModuleDef(local_module)    { ret some(local_module); }
            ExternalModuleDef(*)            { ret none;               }
        }
    }

    #[doc="
        Returns the local module node. Fails if this node does not have a
        local module definition.
    "]
    fn get_local_module() -> @LocalModule {
        alt self.module_def {
            NoModuleDef {
                fail "get_local_module called on a node with no module \
                      definition!";
            }
            LocalModuleDef(local_module) {
                ret local_module;
            }
            ExternalModuleDef(*) {
                fail "get_local_module called on a node with an external \
                      module definition!";
            }
        }
    }

    #[doc="
        Returns the external module node. Fails if this node does not have an
        external module definition.
    "]
    fn get_external_module() -> @ExternalModule {
        alt self.module_def {
            NoModuleDef {
                fail "get_external_module called on a node with no module \
                      definition!";
            }
            LocalModuleDef(*) {
                fail "get_external_module called on a node with a local \
                      module definition!";
            }
            ExternalModuleDef(external_module) {
                ret external_module;
            }
        }
    }

    fn defined_in_namespace(namespace: Namespace) -> bool {
        alt namespace {
            ModuleNamespace { ret self.module_def != NoModuleDef; }
            TypeNamespace   { ret self.type_def != none;          }
            ValueNamespace  { ret self.value_def != none;         }
            ImplNamespace   { ret self.impl_defs.len() >= 0u;     }
        }
    }
}

#[doc="The main resolver class."]
class Resolver {
    let session: session;
    let ast_map: ASTMap;
    let crate: @crate;

    let atom_table: @AtomTable;

    let graph_root: @NameBindings;

    // The number of imports that are currently unresolved.
    let mut unresolved_imports: uint;

    // The module that represents the current item scope.
    let mut current_module: @LocalModule;

    // The current set of local scopes, for values.
    // TODO: Reuse ribs to avoid allocation.
    let value_ribs: @dvec<@Rib>;

    // The atom for the keyword "self".
    let self_atom: Atom;

    let def_map: DefMap;
    let impl_map: ImplMap;

    new(session: session, ast_map: ASTMap, crate: @crate) {
        self.session = session;
        self.ast_map = ast_map;
        self.crate = crate;

        self.atom_table = @AtomTable();

        self.graph_root = @NameBindings();
        (*self.graph_root).define_local_module(NoParentLink);

        self.unresolved_imports = 0u;

        self.current_module = (*self.graph_root).get_local_module();
        self.value_ribs = @dvec();

        self.self_atom = (*self.atom_table).intern(@"self");

        self.def_map = int_hash();
        self.impl_map = int_hash();
    }

    fn resolve(this: @Resolver) {
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
    fn build_reduced_graph(this: @Resolver) {
        let initial_parent =
            LocalModuleParent((*self.graph_root).get_local_module());
        visit_crate(*self.crate, initial_parent, mk_vt(@{
            visit_item: {
                |item, context, visitor|
                (*this).build_reduced_graph_for_item(item, context, visitor)
            },
            visit_view_item: {
                |view_item, context, visitor|
                (*this).build_reduced_graph_for_view_item(view_item, context,
                                                          visitor)
            },
            visit_block: {
                |block, context, visitor|
                (*this).build_reduced_graph_for_block(block, context,
                                                      visitor);
            }
            with *default_visitor()
        }));
    }

    #[doc="
        Returns the current local module tracked by the reduced graph parent.
        If this parent is an external module, fails.
    "]
    fn get_local_module_from_parent(reduced_graph_parent:
                                        ReducedGraphParent)
                                 -> @LocalModule {
        alt reduced_graph_parent {
            ExternalModuleParent(_) {
                fail "get_local_module_from_parent called with an external \
                      module parent!";
            }
            LocalModuleParent(local_module) | BlockParent(local_module, _) {
                ret local_module;
            }
        }
    }

    #[doc="
        Adds a new child item to the module definition of the parent node and
        returns it. Or, if we're inside a block, creates an anonymous module
        corresponding to the innermost block ID instead.

        If this node does not have a module definition and we are not inside
        a block, fails.
    "]
    fn add_child(name: Atom,
                 reduced_graph_parent: ReducedGraphParent)
              -> @NameBindings {

        alt reduced_graph_parent {
            ExternalModuleParent(external_module) {
                alt external_module.children.find(name) {
                    none {
                        let child = @NameBindings();
                        external_module.children.insert(name, child);
                        ret child;
                    }
                    some(child) {
                        ret child;
                    }
                }
            }
            LocalModuleParent(_) | BlockParent(_, _) {
                // If this is the immediate descendant of a local module, then
                // we add the child name directly. Otherwise, we create or
                // reuse an anonymous module and add the child to that.
                
                let mut local_module;
                alt reduced_graph_parent {
                    LocalModuleParent(module) {
                        local_module = module;
                    }
                    BlockParent(module, node_id) {
                        alt module.anonymous_children.find(node_id) {
                            none {
                                local_module = @LocalModule
                                    (BlockParentLink(module, node_id));
                                module.anonymous_children.insert
                                    (node_id, local_module);
                            }
                            some(existing_local_module) {
                                local_module = existing_local_module;
                            }
                        }
                    }
                    ExternalModuleParent(*) { fail; }
                }

                // Add or reuse the child.
                alt local_module.children.find(name) {
                    none {
                        let child = @NameBindings();
                        local_module.children.insert(name, child);
                        ret child;
                    }
                    some(child) {
                        ret child;
                    }
                }
            }
        }
    }

    fn get_local_parent_link(parent: ReducedGraphParent, name: Atom)
                          -> LocalParentLink {
        alt parent {
            LocalModuleParent(local_module) {
                ret LocalModuleParentLink(local_module, name);
            }
            BlockParent(local_module, _) {
                // FIXME: Create the intermediate module, maybe?
                ret LocalModuleParentLink(local_module, name);
            }
            ExternalModuleParent(_) {
                fail "external module parent in get_local_parent_link";
            }
        }
    }

    #[doc="Constructs the reduced graph for one item."]
    fn build_reduced_graph_for_item(item: @item,
                                    parent: ReducedGraphParent,
                                    &&visitor: vt<ReducedGraphParent>) {

        let atom =
            (*self.atom_table).intern(@/* FIXME: bad */ copy item.ident);
        let child = self.add_child(atom, parent);

        alt item.node {
            item_mod(module) {
                (*child).define_local_module
                    (self.get_local_parent_link(parent, atom));
                visit_mod(module, item.span, item.id,
                          LocalModuleParent((*child).get_local_module()),
                          visitor);
            }
            item_native_mod(native_module) {
                (*child).define_local_module
                    (self.get_local_parent_link(parent, atom));
                visit_item(item,
                           LocalModuleParent((*child).get_local_module()),
                           visitor);
            }

            // These items live in the value namespace.
            item_const(*) {
                (*child).define_value(def_const(local_def(item.id)));
            }
            item_fn(decl, _, _) {
                let def = def_fn(local_def(item.id), decl.purity);
                (*child).define_value(def);
                visit_item(item, parent, visitor);
            }

            // These items live in the type namespace.
            item_ty(*) {
                (*child).define_type(def_ty(local_def(item.id)));
            }

            // These items live in both the type and value namespaces.
            item_enum(variants, _, _) {
                (*child).define_type(def_ty(local_def(item.id)));

                for variants.each {
                    |variant|
                    self.build_reduced_graph_for_variant(variant,
                                                         local_def(item.id),
                                                         parent,
                                                         visitor);
                }
            }
            item_res(decl, _, _, _, _, _) {
                let purity = decl.purity;
                let value_def = def_fn(local_def(item.id), purity);
                (*child).define_value(value_def);
                (*child).define_type(def_ty(local_def(item.id)));

                visit_item(item, parent, visitor);
            }
            item_class(_, _, _, ctor, _, _) {
                (*child).define_type(def_ty(local_def(item.id)));

                let purity = ctor.node.dec.purity;
                let ctor_def = def_fn(local_def(ctor.node.id), purity);
                (*child).define_value(ctor_def);

                visit_item(item, parent, visitor);
            }

            item_impl(*) {
                (*child).define_impl(local_def(item.id));
                visit_item(item, parent, visitor);
            }

            item_iface(*) { /* TODO */ }
        }
    }

    #[doc="
        Constructs the reduced graph for one variant. Variants exist in the
        type namespace.
    "]
    fn build_reduced_graph_for_variant(variant: variant,
                                       item_id: def_id,
                                       parent: ReducedGraphParent,
                                       &&_visitor: vt<ReducedGraphParent>) {

        let atom = (*self.atom_table).intern(@/* FIXME: bad */ copy
                                             variant.node.name);
        let child = self.add_child(atom, parent);

        (*child).define_value(def_variant(item_id,
                                          local_def(variant.node.id)));
    }

    #[doc="
        Constructs the reduced graph for one 'view item'. View items consist
        of imports and use directives.
    "]
    fn build_reduced_graph_for_view_item(view_item: @view_item,
                                         parent: ReducedGraphParent,
                                         &&_visitor: vt<ReducedGraphParent>) {
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
                    let local_module =
                        self.get_local_module_from_parent(parent);
                    alt view_path.node {
                        view_path_simple(binding, full_path, _) {
                            let target_atom =
                                (*self.atom_table).intern(@copy binding);
                            let source_atom =
                                (*self.atom_table).intern
                                    (@copy full_path.idents.last());
                            let subclass = @SingleImport(target_atom,
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
                                let subclass = @SingleImport(atom, atom);
                                self.build_import_directive(local_module,
                                                            module_path,
                                                            subclass);
                            }
                        }
                        view_path_glob(_, _) {
                            self.build_import_directive(local_module,
                                                        module_path,
                                                        @GlobImport);
                        }
                    }
                }
            }
            view_item_export(*) { /* TODO */ }
            view_item_use(name, _, node_id) {
                alt find_use_stmt_cnum(self.session.cstore, node_id) {
                    some(crate_id) {
                        let atom = (*self.atom_table).intern(@copy name);
                        let child = self.add_child(atom, parent);

                        let def_id = { crate: crate_id, node: 0 };
                        let parent_link = LocalExternalParentLink
                            (self.get_local_module_from_parent(parent), atom);
                        let external_module =
                            (*child).define_external_module(parent_link,
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

    fn build_reduced_graph_for_block(block: blk,
                                     parent: ReducedGraphParent,
                                     &&visitor: vt<ReducedGraphParent>) {

        let mut new_parent;
        alt parent {
            LocalModuleParent(local_module) | BlockParent(local_module, _) {
                new_parent = BlockParent(local_module, block.node.id);
            }
            ExternalModuleParent(*) {
                fail "unexpected external module parent in \
                      build_reduced_graph_for_block";
            }
        }

        visit_block(block, new_parent, visitor);
    }

    #[doc="
        Builds the reduced graph rooted at the 'use' directive for an external
        crate.
    "]
    fn build_reduced_graph_for_external_crate(root: @ExternalModule) {
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
                let child_name_bindings =
                    self.add_child(atom,
                                   ExternalModuleParent(current_module_node));

                // Define or reuse the module node.
                alt child_name_bindings.module_def {
                    NoModuleDef {
                        #debug("(building reduced graph for external crate) \
                                autovivifying %s", ident);
                        let parent_link =
                            ExternalExternalParentLink(current_module_node,
                                                       atom);
                        current_module_node =
                            (*child_name_bindings).define_external_module
                                (parent_link, none);
                    }
                    ExternalModuleDef(_) {
                        current_module_node =
                            (*child_name_bindings).get_external_module();
                    }
                    LocalModuleDef(_) {
                        fail "unexpected local module";
                    }
                }
            }

            // Add the new child item.
            let atom = (*self.atom_table).intern(@copy final_ident);
            let child_name_bindings =
                self.add_child(atom,
                               ExternalModuleParent(current_module_node));

            alt path_entry.def_like {
                dl_def(def) {
                    alt def {
                        def_mod(def_id) | def_native_mod(def_id) {
                            alt child_name_bindings.module_def {
                                NoModuleDef {
                                    #debug("(building reduced graph for \
                                            external crate) building module \
                                            %s", final_ident);
                                    let parent_link =
                                        ExternalExternalParentLink
                                            (current_module_node, atom);
                                    (*child_name_bindings).
                                        define_external_module
                                            (parent_link, some(def_id));
                                }
                                ExternalModuleDef(external_module) {
                                    #debug("(building reduced graph for \
                                            external crate) filling in def \
                                            id for %s",
                                            final_ident);
                                    external_module.def_id = some(def_id);
                                }
                                LocalModuleDef(_) {
                                    fail "unexpected local module";
                                }
                            }
                        }
                        def_fn(def_id, _) | def_const(def_id) |
                        def_variant(_, def_id) {
                            #debug("(building reduced graph for external \
                                    crate) building value %s", final_ident);
                            (*child_name_bindings).define_value(def);
                        }
                        def_ty(def_id) {
                            #debug("(building reduced graph for external \
                                    crate) building type %s", final_ident);
                            (*child_name_bindings).define_type(def);
                        }
                        def_class(def_id) {
                            #debug("(building reduced graph for external \
                                    crate) building value and type %s",
                                    final_ident);
                            (*child_name_bindings).define_value(def);
                            (*child_name_bindings).define_type(def);
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
                    (*child_name_bindings).define_impl(def_id);
                }
                dl_field {
                    #debug("(building reduced graph for external crate) \
                            ignoring field %s", final_ident);
                }
            }
        }
    }

    #[doc="Creates and adds an import directive to the given module."]
    fn build_import_directive(local_module: @LocalModule,
                              module_path: @dvec<Atom>,
                              subclass: @ImportDirectiveSubclass) {

        let directive = @ImportDirective(module_path, subclass);
        local_module.imports.push(directive);

        // Bump the reference count on the name. Or, if this is a glob, set
        // the appropriate flag.
        alt *subclass {
            SingleImport(target, _) {
                alt local_module.import_resolutions.find(target) {
                    some(resolution) {
                        resolution.outstanding_references += 1u;
                    }
                    none {
                        let resolution = @ImportResolution();
                        resolution.outstanding_references = 1u;
                        local_module.import_resolutions.insert(target,
                                                              resolution);
                            
                    }
                }
            }
            GlobImport {
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
    fn resolve_imports_for_module_subtree(local_module: @LocalModule) {
        #debug("(resolving imports for module subtree) resolving %s",
               self.local_module_to_str(local_module));
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
    fn resolve_imports_for_module(local_module: @LocalModule) {
        if (*local_module).all_imports_resolved() {
            #debug("(resolving imports for module) all imports resolved for \
                   %s",
                   self.local_module_to_str(local_module));
            ret;
        }

        let import_count = local_module.imports.len();
        while local_module.resolved_import_count < import_count {
            let import_index = local_module.resolved_import_count;
            let import_directive = local_module.imports.get_elt(import_index);
            alt self.resolve_import_for_module(local_module,
                                               import_directive) {
                Failed {
                    // We presumably emitted an error. Continue.
                    #debug("!!! (resolving imports for module) error: %s",
                           self.local_module_to_str(local_module));
                }
                Indeterminate {
                    // Bail out. We'll come around next time.
                    break;
                }
                Success(()) {
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
    fn resolve_import_for_module(local_module: @LocalModule,
                                 import_directive: @ImportDirective)
                              -> ResolveResult<()> {

        let mut resolution_result;
        let module_path = import_directive.module_path;

        #debug("(resolving import for module) resolving import '%s::...' in \
                '%s'",
               *(*self.atom_table).atoms_to_str((*module_path).get()),
               self.local_module_to_str(local_module));

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
                Failed {
                    resolution_result = Failed;
                }
                Indeterminate {
                    resolution_result = Indeterminate;
                }
                Success(LocalModuleDef(containing_module)) {
                    // Attempt to resolve the import.
                    alt *import_directive.subclass {
                        SingleImport(target, source) {
                            resolution_result =
                                self.resolve_single_import(local_module,
                                                           containing_module,
                                                           target,
                                                           source);
                        }
                        GlobImport {
                            resolution_result =
                                self.resolve_glob_import(local_module,
                                                         containing_module);
                        }
                    }
                }
                Success(ExternalModuleDef(containing_module)) {
                    alt *import_directive.subclass {
                        SingleImport(target, source) {
                            resolution_result =
                                self.resolve_single_external_import
                                    (local_module,
                                     containing_module,
                                     target,
                                     source);
                        }
                        GlobImport {
                            resolution_result =
                                self.resolve_glob_external_import
                                    (local_module,
                                     containing_module);
                        }
                    }
                }
                Success(NoModuleDef) {
                    fail "NoModuleDef unexpected here";
                }
            }
        }

        // Decrement the count of unresolved imports.
        alt resolution_result {
            Success(()) {
                assert self.unresolved_imports >= 1u;
                self.unresolved_imports -= 1u;
            }
            _ { /* Nothing to do here; just return the error. */ }
        }

        // Decrement the count of unresolved globs if necessary. But only if
        // the resolution result is indeterminate -- otherwise we'll stop
        // processing imports here. (See the loop in
        // resolve_imports_for_module.)
        if resolution_result != Indeterminate {
            alt *import_directive.subclass {
                GlobImport {
                    assert local_module.glob_count >= 1u;
                    local_module.glob_count -= 1u;
                }
                SingleImport(*) { /* Ignore. */ }
            }
        }

        ret resolution_result;
    }

    fn resolve_single_import(local_module: @LocalModule,
                             containing_module: @LocalModule,
                             target: Atom,
                             source: Atom)
                          -> ResolveResult<()> {

        #debug("(resolving single import) resolving '%s' = '%s::%s' from \
                '%s'",
               *(*self.atom_table).atom_to_str(target),
               self.local_module_to_str(containing_module),
               *(*self.atom_table).atom_to_str(source),
               self.local_module_to_str(local_module));

        // We need to resolve all four namespaces for this to succeed.
        //
        // TODO: See if there's some way of handling namespaces in a more
        // generic way. We have four of them; it seems worth doing...
        let mut module_result = UnknownResult;
        let mut value_result = UnknownResult;
        let mut type_result = UnknownResult;
        let mut impl_result = UnknownResult;

        // Search for direct children of the containing module.
        alt containing_module.children.find(source) {
            none { /* Continue. */ }
            some(child_name_bindings) {
                if (*child_name_bindings)
                        .defined_in_namespace(ModuleNamespace) {

                    module_result =
                        BoundResult(LocalTargetModule(containing_module),
                                    child_name_bindings);
                }
                if (*child_name_bindings)
                        .defined_in_namespace(ValueNamespace) {

                    value_result =
                        BoundResult(LocalTargetModule(containing_module),
                                    child_name_bindings);
                }
                if (*child_name_bindings)
                        .defined_in_namespace(TypeNamespace) {

                    type_result =
                        BoundResult(LocalTargetModule(containing_module),
                                    child_name_bindings);
                }
                if (*child_name_bindings)
                        .defined_in_namespace(ImplNamespace) {

                    impl_result =
                        BoundResult(LocalTargetModule(containing_module),
                                    child_name_bindings);
                }
            }
        }

        // Unless we managed to find a result in all four namespaces
        // (exceedingly unlikely), search imports as well.
        alt (module_result, value_result, type_result, impl_result) {
            (BoundResult(*), BoundResult(*), BoundResult(*), BoundResult(*)) {
                // Continue.
            }
            _ {
                // If there is an unresolved glob at this point in the
                // containing module, bail out. We don't know enough to be
                // able to resolve this import.
                if containing_module.glob_count > 0u {
                    #debug("(resolving single import) unresolved glob; \
                            bailing out");
                    ret Indeterminate;
                }

                // Now search the exported imports within the containing
                // module.
                alt containing_module.import_resolutions.find(source) {
                    none {
                        // The containing module definitely doesn't have an
                        // exported import with the name in question. We can
                        // therefore accurately report that the names are
                        // unbound.
                        if module_result == UnknownResult {
                            module_result = UnboundResult;
                        }
                        if value_result == UnknownResult {
                            value_result = UnboundResult;
                        }
                        if type_result == UnknownResult {
                            type_result = UnboundResult;
                        }
                        if impl_result == UnknownResult {
                            impl_result = UnboundResult;
                        }
                    }
                    some(import_resolution)
                            if import_resolution.outstanding_references == 0u {
                        fn get_binding(import_resolution: @ImportResolution,
                                       namespace: Namespace)
                                    -> NamespaceResult {

                            alt (*import_resolution).
                                    target_for_namespace(namespace) {
                                none {
                                    ret UnboundResult;
                                }
                                some(target) {
                                    ret BoundResult(target.target_module,
                                                    target.bindings);
                                }
                            }
                        }

                        // The name is an import which has been fully resolved.
                        // We can, therefore, just follow the import.
                        if module_result == UnknownResult {
                            module_result = get_binding(import_resolution,
                                                        ModuleNamespace);
                        }
                        if value_result == UnknownResult {
                            value_result = get_binding(import_resolution,
                                                       TypeNamespace);
                        }
                        if type_result == UnknownResult {
                            type_result = get_binding(import_resolution,
                                                      ValueNamespace);
                        }
                        if impl_result == UnknownResult {
                            impl_result = get_binding(import_resolution,
                                                      ImplNamespace);
                        }
                    }
                    some(_) {
                        // The import is unresolved. Bail out.
                        #debug("(resolving single import) unresolved import; \
                                bailing out");
                        ret Indeterminate;
                    }
                }
            }
        }

        // We've successfully resolved the import. Write the results in.
        assert local_module.import_resolutions.contains_key(target);
        let import_resolution = local_module.import_resolutions.get(target);

        alt module_result {
            BoundResult(target_module, name_bindings) {
                #debug("(resolving single import) found module binding");
                import_resolution.module_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            UnboundResult {
                #debug("(resolving single import) didn't find module \
                        binding");
            }
            UnknownResult {
                fail "module result should be known at this point";
            }
        }
        alt value_result {
            BoundResult(target_module, name_bindings) {
                import_resolution.value_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            UnboundResult { /* Continue. */ }
            UnknownResult {
                fail "value result should be known at this point";
            }
        }
        alt type_result {
            BoundResult(target_module, name_bindings) {
                import_resolution.type_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            UnboundResult { /* Continue. */ }
            UnknownResult {
                fail "type result should be known at this point";
            }
        }
        alt impl_result {
            BoundResult(target_module, name_bindings) {
                import_resolution.impl_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            UnboundResult { /* Continue. */ }
            UnknownResult {
                fail "impl result should be known at this point";
            }
        }

        assert import_resolution.outstanding_references >= 1u;
        import_resolution.outstanding_references -= 1u;

        #debug("(resolving single import) successfully resolved import");
        ret Success(());
    }

    #[doc="
        Resolves a glob import. Note that this function cannot fail; it either
        succeeds or bails out (as importing * from an empty module or a module
        that exports nothing is valid).
    "]
    fn resolve_glob_import(local_module: @LocalModule,
                           containing_module: @LocalModule)
                        -> ResolveResult<()> {

        // This function works in a highly imperative manner; it eagerly adds
        // everything it can to the list of import resolutions of the module
        // node.

        // We must bail out if the node has unresolved imports of any kind
        // (including globs).
        if !(*containing_module).all_imports_resolved() {
            #debug("(resolving glob import) target module has unresolved \
                    imports; bailing out");
            ret Indeterminate;
        }

        assert containing_module.glob_count == 0u;

        // Add all resolved imports from the containing module.
        for containing_module.import_resolutions.each {
            |atom, target_import_resolution|

            #debug("(resolving glob import) writing module resolution \
                    %? into '%s'",
                   is_none(target_import_resolution.module_target),
                   self.local_module_to_str(local_module));

            // Here we merge two import resolutions.
            alt local_module.import_resolutions.find(atom) {
                none {
                    // Simple: just copy the old import resolution.
                    let new_import_resolution = @ImportResolution();
                    new_import_resolution.module_target =
                        copy target_import_resolution.module_target;
                    new_import_resolution.value_target =
                        copy target_import_resolution.value_target;
                    new_import_resolution.type_target =
                        copy target_import_resolution.type_target;
                    new_import_resolution.impl_target =
                        copy target_import_resolution.impl_target;

                    local_module.import_resolutions.insert
                        (atom, new_import_resolution);
                }
                some(dest_import_resolution) {
                    // Merge the two import resolutions at a finer-grained
                    // level.
                    alt target_import_resolution.module_target {
                        none { /* Continue. */ }
                        some(module_target) {
                            dest_import_resolution.module_target =
                                some(copy module_target);
                        }
                    }
                    alt target_import_resolution.value_target {
                        none { /* Continue. */ }
                        some(value_target) {
                            dest_import_resolution.value_target =
                                some(copy value_target);
                        }
                    }
                    alt target_import_resolution.type_target {
                        none { /* Continue. */ }
                        some(type_target) {
                            dest_import_resolution.type_target =
                                some(copy type_target);
                        }
                    }
                    alt target_import_resolution.impl_target {
                        none { /* Continue. */ }
                        some(impl_target) {
                            dest_import_resolution.impl_target =
                                some(copy impl_target);
                        }
                    }
                }
            }
        }

        // Add all children from the containing module.
        for containing_module.children.each {
            |atom, name_bindings|

            let mut dest_import_resolution;
            alt local_module.import_resolutions.find(atom) {
                none {
                    // Create a new import resolution from this child.
                    dest_import_resolution = @ImportResolution();
                    local_module.import_resolutions.insert
                        (atom, dest_import_resolution);
                }
                some(existing_import_resolution) {
                    dest_import_resolution = existing_import_resolution;
                }
            }


            #error("(resolving glob import) writing module resolution \
                    '%s'",
                   self.local_module_to_str(local_module));

            // Merge the child item into the import resolution.
            let target_module = LocalTargetModule(containing_module);
            if (*name_bindings).defined_in_namespace(ModuleNamespace) {
                dest_import_resolution.module_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            if (*name_bindings).defined_in_namespace(ValueNamespace) {
                dest_import_resolution.value_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            if (*name_bindings).defined_in_namespace(TypeNamespace) {
                dest_import_resolution.type_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            if (*name_bindings).defined_in_namespace(ImplNamespace) {
                dest_import_resolution.impl_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
        }

        #debug("(resolving glob import) successfully resolved import");
        ret Success(());
    }

    // FIXME: This duplicates code from resolve_single_import.
    fn resolve_single_external_import(local_module: @LocalModule,
                                      containing_module: @ExternalModule,
                                      target: Atom,
                                      source: Atom)
                                   -> ResolveResult<()> {

        #debug("(resolving single external import) resolving import '%s' = \
                '%s::%s' in '%s'",
               *(*self.atom_table).atom_to_str(target),
               self.external_module_to_str(containing_module),
               *(*self.atom_table).atom_to_str(source),
               self.local_module_to_str(local_module));

        // We need to resolve all four namespaces for this to succeed.
        let mut module_result = none;
        let mut value_result = none;
        let mut type_result = none;
        let mut impl_result = none;

        // Search for direct children of the containing module.
        alt containing_module.children.find(source) {
            none { /* Continue. */ }
            some(child_name_bindings) {
                if (*child_name_bindings)
                        .defined_in_namespace(ModuleNamespace) {

                    module_result = some(child_name_bindings);
                }
                if (*child_name_bindings)
                        .defined_in_namespace(ValueNamespace) {

                    value_result = some(child_name_bindings);
                }
                if (*child_name_bindings)
                        .defined_in_namespace(TypeNamespace) {

                    type_result = some(child_name_bindings);
                }
                if (*child_name_bindings)
                        .defined_in_namespace(ImplNamespace) {

                    impl_result = some(child_name_bindings);
                }
            }
        }

        // If no namespaces were resolved, that's an error.
        if is_none(module_result) && is_none(value_result) &&
                is_none(type_result) && is_none(impl_result) {
            #debug("!!! (resolving single external import) failed");
            ret Failed;
        }

        // We've successfully resolved the import. Write the results in.
        assert local_module.import_resolutions.contains_key(target);
        let import_resolution = local_module.import_resolutions.get(target);

        let target_module = ExternalTargetModule(containing_module);

        alt module_result {
            none { /* Continue. */ }
            some(name_bindings) {
                #error("(resolving glob import) writing module resolution \
                        '%s'",
                       self.local_module_to_str(local_module));

                import_resolution.module_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
        }
        alt value_result {
            none { /* Continue. */ }
            some(name_bindings) {
                import_resolution.value_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
        }
        alt type_result {
            none { /* Continue. */ }
            some(name_bindings) {
                import_resolution.type_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
        }
        alt impl_result {
            none { /* Continue. */ }
            some(name_bindings) {
                import_resolution.impl_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
        }

        assert import_resolution.outstanding_references >= 1u;
        import_resolution.outstanding_references -= 1u;

        #debug("(resolving external import) success");
        ret Success(());
    }

    // FIXME: This duplicates code from resolve_glob_import.
    fn resolve_glob_external_import(local_module: @LocalModule,
                                    containing_module: @ExternalModule)
                                 -> ResolveResult<()> {

        #debug("(resolving glob external import) resolving");

        // Add all children from the containing module.
        for containing_module.children.each {
            |atom, name_bindings|

            let mut dest_import_resolution;
            alt local_module.import_resolutions.find(atom) {
                none {
                    // Create a new import resolution from this child.
                    dest_import_resolution = @ImportResolution();
                    local_module.import_resolutions.insert
                        (atom, dest_import_resolution);
                }
                some(existing_import_resolution) {
                    dest_import_resolution = existing_import_resolution;
                }
            }

            let target_module = ExternalTargetModule(containing_module);

            // Merge the child item into the import resolution.
            if (*name_bindings).defined_in_namespace(ModuleNamespace) {
                dest_import_resolution.module_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            if (*name_bindings).defined_in_namespace(ValueNamespace) {
                dest_import_resolution.value_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            if (*name_bindings).defined_in_namespace(TypeNamespace) {
                dest_import_resolution.type_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
            if (*name_bindings).defined_in_namespace(ImplNamespace) {
                dest_import_resolution.impl_target =
                    some(ImportResolutionTarget(target_module,
                                                name_bindings));
            }
        }

        #debug("(resolving external glob import) success");
        ret Success(());
    }

    #[doc="
        Attempts to resolve the module part of an import directive rooted at
        the given module.
    "]
    fn resolve_module_path_for_import(local_module: @LocalModule,
                                      module_path: @dvec<Atom>)
                                   -> ResolveResult<ModuleDef> {

        let module_path_len = (*module_path).len();
        assert module_path_len > 0u;

        #debug("(resolving module path for import) processing '%s' rooted at \
               '%s'",
               *(*self.atom_table).atoms_to_str((*module_path).get()),
               self.local_module_to_str(local_module));

        // The first element of the module path must be in the current scope
        // chain.
        let first_element = (*module_path).get_elt(0u);
        let mut search_module_def;
        alt self.resolve_module_in_lexical_scope(local_module, first_element) {
            Failed {
                #error("(resolving module path for import) !!! unresolved \
                        name: %s",
                       *(*self.atom_table).atom_to_str(first_element));

                ret Failed;
            }
            Indeterminate {
                #debug("(resolving module path for import) indeterminate; \
                        bailing");
                ret Indeterminate;
            }
            Success(resulting_module_def) {
                search_module_def = resulting_module_def;
            }
        }

        // Now resolve the rest of the path. This does not involve looking
        // upward though scope chains; we simply resolve names directly in
        // modules as we go.
        let mut index = 1u;
        while index < module_path_len {
            let name = (*module_path).get_elt(index);
            alt self.resolve_name_in_module(search_module_def,
                                            name,
                                            ModuleNamespace) {

                Failed {
                    #debug("!!! (resolving module path for import) module \
                           resolution failed: %s",
                           *(*self.atom_table).atom_to_str(name));
                    ret Failed;
                }
                Indeterminate {
                    #debug("(resolving module path for import) module \
                           resolution is indeterminate: %s",
                           *(*self.atom_table).atom_to_str(name));
                    ret Indeterminate;
                }
                Success(target) {
                    alt target.bindings.module_def {
                        NoModuleDef {
                            // Not a module.
                            #debug("!!! (resolving module path for import) \
                                   not a module: %s",
                                   *(*self.atom_table).atom_to_str(name));
                            ret Failed;
                        }
                        LocalModuleDef(*) | ExternalModuleDef(*) {
                            search_module_def = target.bindings.module_def;
                        }
                    }
                }
            }

            index += 1u;
        }

        #debug("(resolving module path for import) resolved module");
        ret Success(search_module_def);
    }

    fn resolve_item_in_lexical_scope(local_module: @LocalModule,
                                     name: Atom,
                                     namespace: Namespace)
                                  -> ResolveResult<ImportResolutionTarget> {

        #debug("(resolving item in lexical scope) resolving '%s' in \
                namespace %? in '%s'",
               *(*self.atom_table).atom_to_str(name),
               namespace,
               self.local_module_to_str(local_module));

        // The current module node is handled specially. First, check for
        // its immediate children.
        alt local_module.children.find(name) {
            some(name_bindings)
                    if (*name_bindings).defined_in_namespace(namespace) {

                let target_module = LocalTargetModule(local_module);
                ret Success(ImportResolutionTarget(target_module,
                                                   name_bindings));
            }
            some(_) | none { /* Not found; continue. */ }
        }

        // Now check for its import directives. We don't have to have resolved
        // all its imports in the usual way; this is because chains of
        // adjacent import statements are processed as though they mutated the
        // current scope.
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
                    some(target) {
                        ret Success(copy target);
                    }
                }
            }
        }
        
        // Finally, proceed up the scope chain looking for parent modules.
        let mut search_module = local_module;
        loop {
            // Go to the next parent.
            alt search_module.parent_link {
                NoParentLink {
                    // No more parents. This module was unresolved.
                    #debug("(resolving item in lexical scope) unresolved \
                            module");
                    ret Failed;
                }
                LocalModuleParentLink(parent_module_node, _) |
                BlockParentLink(parent_module_node, _) {
                    search_module = parent_module_node;
                }
            }

            // Resolve the name in the parent module.
            alt self.resolve_name_in_local_module(search_module,
                                                  name,
                                                  namespace) {
                Failed {
                    // Continue up the search chain.
                }
                Indeterminate {
                    // We couldn't see through the higher scope because of an
                    // unresolved import higher up. Bail.
                    #debug("(resolving item in lexical scope) indeterminate \
                            higher scope; bailing");
                    ret Indeterminate;
                }
                Success(target) {
                    // We found the module.
                    ret Success(copy target);
                }
            }
        }
    }

    fn resolve_module_in_lexical_scope(local_module: @LocalModule,
                                       name: Atom)
                                    -> ResolveResult<ModuleDef> {

        alt self.resolve_item_in_lexical_scope(local_module,
                                               name,
                                               ModuleNamespace) {

            Success(target) {
                alt target.bindings.module_def {
                    NoModuleDef {
                        #error("!!! (resolving module in lexical scope) module
                                wasn't actually a module!");
                        ret Failed;
                    }
                    LocalModuleDef(*) | ExternalModuleDef(*) {
                        ret Success(target.bindings.module_def);
                    }
                }
            }
            Indeterminate {
                #debug("(resolving module in lexical scope) indeterminate; \
                        bailing");
                ret Indeterminate;
            }
            Failed {
                #debug("(resolving module in lexical scope) failed to \
                        resolve");
                ret Failed;
            }
        }
    }

    #[doc="
        Attempts to resolve the supplied name in the given module for the
        given namespace. If successful, returns the reduced graph node
        corresponding to the name.
    "]
    fn resolve_name_in_module(module_def: ModuleDef,
                              name: Atom,
                              namespace: Namespace)
                           -> ResolveResult<ImportResolutionTarget> {

        alt module_def {
            NoModuleDef {
                fail "(resolving name in module) unexpected NoModuleDef";
            }
            LocalModuleDef(local_module) {
                ret self.resolve_name_in_local_module(local_module,
                                                      name,
                                                      namespace);
            }
            ExternalModuleDef(external_module) {
                ret self.resolve_name_in_external_module(external_module,
                                                         name,
                                                         namespace);
            }
        }
    }

    fn resolve_name_in_local_module(local_module: @LocalModule,
                                    name: Atom,
                                    namespace: Namespace)
                                 -> ResolveResult<ImportResolutionTarget> {

        #debug("(resolving name in local module) resolving '%s' in '%s'",
               *(*self.atom_table).atom_to_str(name),
               self.local_module_to_str(local_module));

        // First, check the direct children of the module.
        alt local_module.children.find(name) {
            some(name_bindings)
                    if (*name_bindings).defined_in_namespace(namespace) {

                #debug("(resolving name in local module) found node as \
                        child");
                let target_module = LocalTargetModule(local_module);
                ret Success(ImportResolutionTarget(target_module,
                                                   name_bindings));
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
            ret Indeterminate;
        }

        // Otherwise, we check the list of resolved imports.
        alt local_module.import_resolutions.find(name) {
            some(import_resolution) {
                if import_resolution.outstanding_references != 0u {
                    #debug("(resolving name in local module) import \
                            unresolved; bailing out");
                    ret Indeterminate;
                }

                alt (*import_resolution).target_for_namespace(namespace) {
                    none { /* Continue. */ }
                    some(target) {
                        #debug("(resolving name in local module) resolved to \
                                import");
                        ret Success(copy target);
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
        ret Failed;
    }

    #[doc="
        Resolves a one-level renaming import of the kind `import foo = bar;`
        This needs special handling, as, unlike all of the other imports, it
        needs to look in the scope chain for modules and non-modules alike.
    "]
    fn resolve_one_level_renaming_import(local_module: @LocalModule,
                                         import_directive: @ImportDirective)
                                      -> ResolveResult<()> {

        let mut target_name;
        let mut source_name;
        alt *import_directive.subclass {
            SingleImport(target, source) {
                target_name = target;
                source_name = source;
            }
            GlobImport {
                fail "found `import *`, which is invalid";
            }
        }

        #debug("(resolving one-level naming result) resolving import '%s' = \
                '%s' in '%s'",
                *(*self.atom_table).atom_to_str(target_name),
                *(*self.atom_table).atom_to_str(source_name),
                self.local_module_to_str(local_module));

        // Find the matching items in the lexical scope chain for every
        // namespace. If any of them come back indeterminate, this entire
        // import is indeterminate.
        let mut module_result;
        #debug("(resolving one-level naming result) searching for module");
        alt self.resolve_item_in_lexical_scope(local_module,
                                               source_name,
                                               ModuleNamespace) {

            Failed {
                #debug("(resolving one-level renaming import) didn't find \
                        module result");
                module_result = none;
            }
            Indeterminate {
                #debug("(resolving one-level renaming import) module result \
                        is indeterminate; bailing");
                ret Indeterminate;
            }
            Success(name_bindings) {
                #debug("(resolving one-level renaming import) module result \
                        found");
                module_result = some(copy name_bindings);
            }
        }

        let mut value_result;
        #debug("(resolving one-level naming result) searching for value");
        alt self.resolve_item_in_lexical_scope(local_module,
                                               source_name,
                                               ValueNamespace) {

            Failed {
                #debug("(resolving one-level renaming import) didn't find \
                        value result");
                value_result = none;
            }
            Indeterminate {
                #debug("(resolving one-level renaming import) value result is \
                        indeterminate; bailing");
                ret Indeterminate;
            }
            Success(name_bindings) {
                #debug("(resolving one-level renaming import) value result \
                        found");
                value_result = some(copy name_bindings);
            }
        }

        let mut type_result;
        #debug("(resolving one-level naming result) searching for type");
        alt self.resolve_item_in_lexical_scope(local_module,
                                               source_name,
                                               TypeNamespace) {

            Failed {
                #debug("(resolving one-level renaming import) didn't find \
                        type result");
                type_result = none;
            }
            Indeterminate {
                #debug("(resolving one-level renaming import) type result is \
                        indeterminate; bailing");
                ret Indeterminate;
            }
            Success(name_bindings) {
                #debug("(resolving one-level renaming import) type result \
                        found");
                type_result = some(copy name_bindings);
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
        alt self.resolve_item_in_lexical_scope(local_module,
                                               source_name,
                                               ImplNamespace) {

            Failed {
                #debug("(resolving one-level renaming import) didn't find \
                        impl result");
                impl_result = none;
            }
            Indeterminate {
                #debug("(resolving one-level renaming import) impl result is \
                        indeterminate; bailing");
                ret Indeterminate;
            }
            Success(name_bindings) {
                #debug("(resolving one-level renaming import) impl result \
                        found");
                impl_result = some(copy name_bindings);
            }
        }

        // If nothing at all was found, that's an error.
        if is_none(module_result) && is_none(value_result) &&
                is_none(type_result) && is_none(impl_result) {
            #error("!!! (resolving one-level renaming import) couldn't find \
                    anything with that name");
            ret Failed;
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
                       is_none(module_result),
                       *(*self.atom_table).atom_to_str(target_name),
                       self.local_module_to_str(local_module));

                import_resolution.module_target = module_result;
                import_resolution.value_target = value_result;
                import_resolution.type_target = type_result;
                import_resolution.impl_target = impl_result;

                assert import_resolution.outstanding_references >= 1u;
                import_resolution.outstanding_references -= 1u;
            }
        }

        #debug("(resolving one-level renaming import) successfully resolved");
        ret Success(());
    }

    fn resolve_name_in_external_module(parent_module: @ExternalModule,
                                       name: Atom,
                                       namespace: Namespace)
                                    -> ResolveResult<ImportResolutionTarget> {

        #debug("(resolving name in external module) resolving '%s' in \
                external",
                *(*self.atom_table).atom_to_str(name));

        alt parent_module.children.find(name) {
            some(name_bindings)
                    if (*name_bindings).defined_in_namespace(namespace) {

                // The node is a direct child.
                #debug("(resolving name in external module) found node as \
                        child");
                let target_module = ExternalTargetModule(parent_module);
                ret Success(ImportResolutionTarget(target_module,
                                                   name_bindings));
            }
            some(_) | none {
                // We're out of luck.
                #debug("(resolving name in external module) failed");
                ret Failed;
            }
        }
    }

    fn report_unresolved_imports(name_bindings: @NameBindings) {
        let mut local_module;
        alt (*name_bindings).get_local_module_if_available() {
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
                   self.local_module_to_str(local_module),
                   *(*self.atom_table).atoms_to_str((*module_path).get()));
        }

        // Descend into children.
        for local_module.children.each {
            |_name, child_node|
            self.report_unresolved_imports(child_node);
        }
    }

    // AST resolution: We simply build up a list of scopes.

    fn with_scope(name: option<Atom>, f: fn()) {
        let orig_module = self.current_module;

        // Move down in the graph.
        alt name {
            none { /* Nothing to do. */ }
            some(name) {
                alt orig_module.children.find(name) {
                    none {
                        #debug("!!! (with scope) didn't find '%s' in '%s'",
                               *(*self.atom_table).atom_to_str(name),
                               self.local_module_to_str(orig_module));
                    }
                    some(name_bindings) {
                        alt (*name_bindings).get_local_module_if_available() {
                            none {
                                #debug("!!! (with scope) didn't find local \
                                        module for '%s' in '%s'",
                                       *(*self.atom_table).atom_to_str(name),
                                       self.local_module_to_str(orig_module));
                            }
                            some(local_module) {
                                self.current_module = local_module;
                            }
                        }
                    }
                }
            }
        }

        f();

        self.current_module = orig_module;
    }

    fn search_ribs(ribs: @dvec<@Rib>, name: Atom) -> option<def_like> {
        // FIXME: This should not use a while loop.
        // TODO: Try caching?
        let mut i = (*ribs).len();
        while i != 0u {
            i -= 1u;
            let Rib = (*ribs).get_elt(i);
            alt Rib.bindings.find(name) {
                some(def_like) { ret some(def_like); }
                none { /* Continue. */ }
            }
        }

        ret none;
    }

    fn resolve_crate() unsafe {
        #debug("(resolving crate) starting");
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
            },
            visit_expr: {
                |expr, _context, visitor|
                (*this).resolve_expr(expr, visitor);
            },
            visit_local: {
                |local, _context, visitor|
                (*this).resolve_local(local, visitor);
            }
            with *default_visitor()
        }));
    }

    fn resolve_item(item: @item, visitor: ResolveVisitor) {
        #debug("(resolving item) resolving %s", copy item.ident);

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
                    self.resolve_function(method.decl, some(method.tps),
                                          method.body,
                                          HasSelfBinding(item.id),
                                          visitor);
                }
            }
            item_iface(_, _, methods) {
                // Create a new scope for the interface-wide type parameters.
                for methods.each {
                    |method|
                    // We also need a new scope for the method-specific
                    // type parameters.
                    visit_ty(method.decl.output, (), visitor);
                }
            }
            item_class(*) {
                // Create a new scope for the class-wide type parameters.
                // FIXME: Handle methods properly.
                visit_item(item, (), visitor);
            }
            item_mod(module) {
                let atom = (*self.atom_table).intern(@copy item.ident);
                self.with_scope(some(atom)) {
                    ||

                    self.resolve_module(module, item.span, item.ident,
                                        item.id, visitor);
                }
            }
            item_native_mod(native_module) {
                let atom = (*self.atom_table).intern(@copy item.ident);
                self.with_scope(some(atom)) {
                    ||

                    for native_module.items.each {
                        |native_item|
                        alt native_item.node {
                            native_item_fn(*) {
                                visit_native_item(native_item, (), visitor);
                            }
                        }
                    }
                }
            }
            item_fn(fn_decl, ty_params, block) {
                self.resolve_function(fn_decl, some(ty_params), block,
                                      NoSelfBinding, visitor);
            }
            item_res(*) | item_const(*) {
                visit_item(item, (), visitor);
            }
        }
    }

    fn resolve_function(fn_decl: fn_decl,
                        _ty_params: option<[ty_param]>,
                        block: blk,
                        self_binding: SelfBinding,
                        visitor: ResolveVisitor) {

        // Create a Rib for the function.
        let function_rib = @Rib();
        (*self.value_ribs).push(function_rib);

        // Add self to the Rib, if necessary.
        alt self_binding {
            NoSelfBinding { /* Nothing to do. */ }
            HasSelfBinding(self_node_id) {
                let def_like = dl_def(def_self(self_node_id));
                (*function_rib).bindings.insert(self.self_atom, def_like);
            }
        }

        // Add each argument to the Rib.
        for fn_decl.inputs.each {
            |argument|

            let name = (*self.atom_table).intern(@copy argument.ident);
            let def_like = dl_def(def_arg(argument.id, argument.mode));
            (*function_rib).bindings.insert(name, def_like);

            #debug("(resolving function) recorded argument '%s'",
                   *(*self.atom_table).atom_to_str(name));
        }

        // Note: We don't call resolve_block() because that would create a
        // useless extra Rib for the outermost function block.
        visit_block(block, (), visitor);

        #debug("(resolving function) leaving function");

        (*self.value_ribs).pop();
    }

    fn resolve_module(module: _mod, span: span, _name: ident, id: node_id,
                      visitor: ResolveVisitor) {

        visit_mod(module, span, id, (), visitor);
    }

    fn resolve_local(local: @local, _visitor: ResolveVisitor) {
        let mut mutability;
        if local.node.is_mutbl {
            mutability = Mutable;
        } else {
            mutability = Immutable;
        };

        self.resolve_pattern(local.node.pat, IrrefutableMode, mutability);
    }

    fn resolve_arm(arm: arm, visitor: ResolveVisitor) {
        for arm.pats.each {
            |pattern|
            self.resolve_pattern(pattern, RefutableMode, Immutable);
        }

        visit_expr_opt(arm.guard, (), visitor);
        self.resolve_block(arm.body, visitor);
    }

    fn resolve_block(block: blk, visitor: ResolveVisitor) {
        #debug("(resolving block) entering block");
        (*self.value_ribs).push(@Rib());

        // Move down in the graph, if there's an anonymous module rooted here.
        let orig_module = self.current_module;
        alt self.current_module.anonymous_children.find(block.node.id) {
            none { /* Nothing to do. */ }
            some(anonymous_module) {
                #debug("(resolving block) found anonymous module");
                self.current_module = anonymous_module;
            }
        }

        // Descend into the block.
        visit_block(block, (), visitor);

        // Move back up.
        self.current_module = orig_module;

        (*self.value_ribs).pop();
        #debug("(resolving block) leaving block");
    }

    fn resolve_pattern(pattern: @pat,
                       _mode: PatternBindingMode,
                       mutability: Mutability) {

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

                    #debug("(resolving pattern) binding '%s'",
                           path.idents[0]);

                    let atom =
                        (*self.atom_table).intern(@copy path.idents[0]);
                    let is_mutable = mutability == Mutable;
                    let def_like = dl_def(def_local(pattern.id, is_mutable));
                    (*self.value_ribs).last().bindings.insert(atom, def_like);
                }
                _ {
                    /* Nothing to do. FIXME: Handle more cases. */
                }
            }
        }
    }

    fn resolve_expr(expr: @expr, visitor: ResolveVisitor) {
        alt expr.node {
            // The interpretation of paths depends on whether the path has
            // multiple elements in it or not.
            expr_path(path) if path.idents.len() == 1u {
                // This is a local path in the value namespace. Walk through
                // scopes looking for it.

                let name = (*self.atom_table).intern(@copy path.idents[0]);

                // First, check the local set of ribs.
                let mut result_def;
                alt self.search_ribs(self.value_ribs, name) {
                    some(dl_def(def)) {
                        #debug("(resolving expr) resolved '%s' to local",
                               *(*self.atom_table).atom_to_str(name));
                        result_def = some(def);
                    }
                    some(dl_field) | some(dl_impl(_)) | none {
                        // Otherwise, check the items.
                        alt self.resolve_item_in_lexical_scope
                                (self.current_module, name, ValueNamespace) {

                            Success(target) {
                                alt target.bindings.value_def {
                                    none {
                                        fail "resolved name in value namespace
                                              to a graph node with no value
                                              def?!";
                                    }
                                    some(def) {
                                        #debug("(resolving expr) resolved '%s'
                                                to item",
                                               *(*self.atom_table).
                                                atom_to_str(name));
                                        result_def = some(def);
                                    }
                                }
                            }
                            Indeterminate {
                                fail "unexpected indeterminate result";
                            }
                            Failed {
                                result_def = none;
                            }
                        }
                    }
                }

                alt result_def {
                    some(def) {
                        // Write the result into the def map.
                        self.def_map.insert(expr.id, def);
                    }
                    none {
                        self.session.span_warn
                            (expr.span,
                             #fmt("use of undeclared identifier '%s'",
                                  *(*self.atom_table).atom_to_str(name)));
                    }
                }
            }

            expr_fn(_, fn_decl, block, _) | expr_fn_block(fn_decl, block, _) {
                self.resolve_function(fn_decl, none, block, NoSelfBinding,
                                      visitor);
            }

            _ {
                visit_expr(expr, (), visitor);
            }
        }
    }

    // Diagnostics

    #[doc="
        A terribly inefficient routine to print out the name of a local
        module.
    "]
    fn local_module_to_str(local_module: @LocalModule) -> str {
        let atoms = dvec();
        let mut current_local_module = local_module;
        loop {
            alt current_local_module.parent_link {
                NoParentLink {
                    break;
                }
                LocalModuleParentLink(local_module, name) {
                    atoms.push(name);
                    current_local_module = local_module;
                }
                BlockParentLink(local_module, node_id) {
                    atoms.push((*self.atom_table).intern(@"<opaque>"));
                    current_local_module = local_module;
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

    fn external_module_to_str(_external_module: @ExternalModule) -> str {
        ret "<external>";
    }

    fn dump_local_module(local_module: @LocalModule) {
        #debug("Dump of module '%s':",
               self.local_module_to_str(local_module));

        #debug("Children:");
        for local_module.children.each {
            |name, _child|

            #debug("* %s", *(*self.atom_table).atom_to_str(name));
        }

        #debug("Import resolutions:");
        for local_module.import_resolutions.each {
            |name, import_resolution|

            let mut module_repr;
            alt (*import_resolution).target_for_namespace(ModuleNamespace) {
                none { module_repr = ""; }
                some(target) {
                    module_repr = " module:?";
                    // FIXME
                }
            }

            let mut value_repr;
            alt (*import_resolution).target_for_namespace(ValueNamespace) {
                none { value_repr = ""; }
                some(target) {
                    value_repr = " value:?";
                    // FIXME
                }
            }

            let mut type_repr;
            alt (*import_resolution).target_for_namespace(TypeNamespace) {
                none { type_repr = ""; }
                some(target) {
                    type_repr = " type:?";
                    // FIXME
                }
            }

            let mut impl_repr;
            alt (*import_resolution).target_for_namespace(ImplNamespace) {
                none { impl_repr = ""; }
                some(target) {
                    impl_repr = " impl:?";
                    // FIXME
                }
            }

            #debug("* %s:%s%s%s%s",
                   *(*self.atom_table).atom_to_str(name),
                   module_repr, value_repr, type_repr, impl_repr);
        }
    }
}

#[doc="Entry point to crate resolution."]
fn resolve_crate(session: session, ast_map: ASTMap, crate: @crate)
              -> { def_map: DefMap, impl_map: ImplMap } {

    let resolver = @Resolver(session, ast_map, crate);
    (*resolver).resolve(resolver);
    ret { def_map: resolver.def_map, impl_map: resolver.impl_map };
}

