import syntax::{ast, ast_util, visit};
import syntax::codemap::span;
import ast::*;
import ast_util::{hash_def, local_def, def_id_of_def, new_def_hash, path_name};
import ast_util::{walk_pat};
import driver::session::session;
import metadata::{csearch, cstore};
import syntax::ast_map;

import std::map::{hashmap, str_hash, int_hash};
import std::list;
import list::{cons, nil};

// FIXME either build up an exp_map or change the code (metadata
// encoder, reachability checker) to no longer need it
// FIXME check for duplicate names
// FIXME check for unused imports?

// Resolution in Rust is slightly tricky because there is no obvious
// dependency order between modules -- A can import from B, and B can
// import from A at the same time.
//
// This resolver first builds up a 'tree' of scopes (as a set of
// structure-sharing lists), some of which -- the ones that depend on
// other scopes -- are not filled in yet, and will fill themselves in
// when first used or when explicitly forced. An array of
// paths-to-be-resolved along with their local scope is also built up
// by this first pass.
//
// Next, all unfinished scopes are forced. Forcing one scope, for
// example an import scope, might trigger the forcing of other scopes.
// During the resolution of an import, that import 'turns itself off',
// in order to prevent accidental cyclic references.
//
// Finally, the paths are looked up using the (now finished) scope
// lists, and the definition identifiers are stored in the def_map.
//
// Impl scopes work differently from regular value/module/type scopes,
// so they are handled in a separate pass, which builds up a list of
// sets of impls, which the typechecker uses to resolve methods,
// casts, and bounded parameters.

// The data structures built by this pass
type def_map = hashmap<node_id, def>;
type impl_map = hashmap<node_id, iscopes>;

// A cache for crate-external definitions
type ext_key = {did: def_id, ns: ns, ident: str};
type ext_map = hashmap<ext_key, def>;
fn ext_hash() -> ext_map {
    fn hash(v: ext_key) -> uint {
        str::hash(v.ident) + hash_def(v.did) + v.ns as uint
    }
    std::map::hashmap(hash, {|a, b| a == b})
}

type ctxt = @{mod_map: hashmap<def_id, scope>,
              // Used to error about (non-glob) imports that don't
              // resolve to anything (non-local since it depends on
              // both the impl resolution and regular resolution)
              okay_imports: hashmap<node_id, ()>,
              // Unresolved names that have already been reported
              mut reported: [ident],
              ast_map: ast_map::map,
              def_map: def_map,
              ext_map: ext_map,
              // Scopes that need to be forced
              mut fixups: [delayed_scope],
              // Paths that have to be resolved
              mut paths: [{id: node_id, sc: scopes, pth: @path, ns: ns}],
              // Cached top-level scope, for resolving ::global::paths
              mut top_scope: scopes,
              // Cache of impl scopes
              iscope_per_mod: hashmap<def_id, option<iscope>>,
              impl_map: impl_map,
              crate: @crate,
              sess: session};

fn resolve_crate(sess: session, amap: ast_map::map, crate: @crate)
    -> {def_map: def_map, impl_map: impl_map} {
    let cx = @{mod_map: new_def_hash(),
               okay_imports: int_hash(),
               mut reported: [],
               ast_map: amap,
               def_map: int_hash(),
               ext_map: ext_hash(),
               mut fixups: [],
               mut paths: [],
               mut top_scope: @nil,
               iscope_per_mod: new_def_hash(),
               impl_map: int_hash(),
               crate: crate,
               sess: sess};
    build_scopes(cx, crate);
    cx.top_scope = ext(ext(@nil, top_scope as scope),
                       cx.mod_scope(def_mod(local_def(crate_node_id))));
    force_delayed(cx);
    resolve_paths(cx);
    resolve_impls(cx, crate);
    sess.abort_if_errors();
    {def_map: cx.def_map, impl_map: cx.impl_map}
}

impl util for ctxt {
    fn err(s: span, msg: str) { self.sess.span_err(s, msg); }
    fn note(s: span, msg: str) { self.sess.span_note(s, msg); }
    // Lookup a scope for a mod. Only works after the build pass has
    // completed
    fn mod_scope(def: def) -> scope {
        let id = def_id_of_def(def);
        alt self.mod_map.find(id) {
          some(s) { ret s; }
          none {
            // Local mods should have been added by the build pass
            assert id.crate != local_crate;
            let ext_scope = ext_mod_scope(self, id);
            self.mod_map.insert(id, ext_scope);
            ext_scope
          }
        }
    }
}

// Rust names live in three different namespaces: modules, values, and types
enum ns { ns_mod, ns_val, ns_typ }

// Given a def, return the namespace it belongs in
fn ns_for_def(d: def) -> ns {
    alt d {
      ast::def_mod(*) | ast::def_native_mod(*) { ns_mod }
      ast::def_variant(*) | ast::def_fn(*) | ast::def_self(*) |
      ast::def_const(*) | ast::def_arg(*) | ast::def_local(*) |
      ast::def_upvar(*) { ns_val }
      ast::def_ty_param(*) | ast::def_prim_ty(*) | ast::def_class(*) |
      ast::def_ty(*) | ast::def_binding(*) | ast::def_use(_) { ns_typ }
      ast::def_region(*) { fail "regions are not handled by this pass" }
    }
}

// Used to enforce non-closing functions not referring to local names
// in their parent functions.
fn def_is_local(d: def) -> bool {
    alt d {
      ast::def_arg(*) | ast::def_local(*) | ast::def_binding(*) |
      ast::def_upvar(*) | ast::def_self(*) | ast::def_ty_param(*) { true }
      _ { false }
    }
}

// Lookup result
enum res {
    found(def),
    not_found,
    // This last value signals that the name was not found, not
    // necessarily because it wasn't present, but because some other
    // error was encountered. No additional errors should be reported
    // about this lookup.
    not_found_err
}

// Scope objects (usually used in list form)

iface scope {
    fn lookup(i: ident, ns: ns) -> res;
}

enum scope_elt { scope(scope), bound_close(node_id), bound_item }
type scopes = @list::list<scope_elt>;

fn ext(sc: scopes, s: scope) -> scopes { @cons(scope(s), sc) }

impl of scope for () {
    fn lookup(_i: ident, _ns: ns) -> res { not_found }
}

impl of scope for {ident: ident, def: def, ns: ns} {
    fn lookup(i: ident, ns: ns) -> res {
        if ns == self.ns && i == self.ident { found(self.def) }
        else { not_found }
    }
}
fn single_def(i: ident, def: def, ns: ns) -> scope {
    {ident: i, def: def, ns: ns} as scope
}

type deflist = [{ident: ident, def: def}];
fn lookup(i: ident, l: deflist) -> res {
    for l.each {|a| if a.ident == i { ret found(a.def); } }
    not_found
}

impl of scope for {lst: deflist, ns: ns} {
    fn lookup(i: ident, ns: ns) -> res {
        if ns == self.ns { lookup(i, self.lst) } else { not_found }
    }
}
fn multi_def(lst: deflist, ns: ns) -> scope {
    {lst: lst, ns: ns} as scope
}

type mix_set = {mods: deflist, vals: deflist, typs: deflist};
impl of scope for mix_set {
    fn lookup(i: ident, ns: ns) -> res {
        alt ns { ns_mod { lookup(i, self.mods) }
                 ns_val { lookup(i, self.vals) }
                 ns_typ { lookup(i, self.typs) } }
    }
}

type delayed_scope = @{
    mut done: option<scope>,
    finish_fn: fn@() -> option<scope>,
};
impl of scope for delayed_scope {
    fn lookup(i: ident, ns: ns) -> res {
        alt self.done {
          some(scp) { scp.lookup(i, ns) }
          none {
            alt self.finish_fn() {
              some(s) { self.done = some(s); s.lookup(i, ns) }
              none { not_found }
            }
          }
        }
    }
}
fn delayed_scope(cx: ctxt, fin: fn@() -> option<scope>) -> scope {
    let val = @{mut done: none, finish_fn: fin};
    cx.fixups += [val];
    val as scope
}
fn force_delayed(cx: ctxt) {
    let mut fixups = [];
    fixups <-> cx.fixups; // Prevent alias errors
    for fixups.each {|d|
        if d.done == none { d.done = d.finish_fn(); }
    }
}

fn arg_scope(decl: fn_decl) -> scope {
    let args = decl.inputs.map {|a|
        {ident: a.ident, def: def_arg(a.id, a.mode)}
    };
    multi_def(args, ns_val)
}

enum pat_bind_mode { binding, local(bool) }
// The meaning of pat_ident depends on whether an enum variant with
// that name is in scope. The probing lookup has to be careful not to
// emit spurious errors. Only matching patterns (alt) can match
// nullary variants. For binding patterns (let), matching such a
// variant is simply disallowed (since it's rarely what you want).
fn resolve_pat(cx: ctxt, sc: scopes, p: @pat, mode: pat_bind_mode) {
    walk_pat(p) {|p|
        alt p.node {
          pat_ident(pth, none) {
            alt lookup_path(cx, sc, pth, ns_val, false) {
              found(d@def_variant(*)) {
                if mode == binding {
                    cx.def_map.insert(p.id, d);
                } else {
                    cx.err(p.span, "declaration of `" + path_name(pth) +
                           "` shadows an enum that's in scope");
                }
              }
              _ {}
            }
          }
          pat_enum(pth, _) {
            alt lookup_path_strict(cx, sc, pth, ns_val) {
              found(d@def_variant(*)) {
                cx.def_map.insert(p.id, d);
              }
              found(_) {
                cx.err(p.span, "not an enum variant: `" +
                       path_name(pth) + "`");
              }
              _ {}
            }
          }
          _ {}
        }
    }
}
fn pat_scope(cx: ctxt, sc: scopes, p: @pat, mode: pat_bind_mode) -> scope {
    delayed_scope(cx) {||
        let mut lst = [];
        walk_pat(p) {|p|
            resolve_pat(cx, sc, p, mode);
            alt p.node {
              pat_ident(pth, _) {
                if !cx.def_map.contains_key(p.id) {
                    lst += [{ident: pth.idents.last(),
                             def: alt mode {
                               binding { def_binding(p.id) }
                               local(m) { def_local(p.id, m) }
                             }}];
                }
              }
              _ {}
            }
        }
        some({lst: lst, ns: ns_val} as scope)
    }
}

fn import_scope(cx: ctxt, sc: scopes, p: @view_path) -> scope {
    fn mod_val_and_typ(&mods: deflist, &vals: deflist, &typs: deflist,
                       f: fn(ns, &deflist) -> bool) -> bool {
        f(ns_mod, mods) | f(ns_val, vals) | f(ns_typ, typs)
    }
    let resolving_now = @mut false;

    delayed_scope(cx, fn@() -> option<scope> {
        if *resolving_now { ret none; }
        *resolving_now = true;
        let mut mods = [], vals = [], typs = [], err = false;
        alt check p.node {
          view_path_simple(nm, path, id) {
            if path.idents.len() == 1u {
                if mod_val_and_typ(mods, vals, typs, {|ns, lst|
                    alt lookup_in_scopes(cx, path.span, sc,
                                         path.idents.last(), ns) {
                      found(def) { lst += [{ident: nm, def: def}]; true }
                      _ { false }
                    }
                }) { cx.okay_imports.insert(id, ()); }
            } else {
                let mod_path = @{idents: vec::init(path.idents) with *path};
                alt lookup_path_strict(cx, sc, mod_path, ns_mod) {
                  found(def) {
                    cx.def_map.insert(id, def);
                    let mod_s = cx.mod_scope(def);
                    if mod_val_and_typ(mods, vals, typs, {|ns, lst|
                        alt mod_s.lookup(path.idents.last(), ns) {
                          found(def) { lst += [{ident: nm, def: def}]; true }
                          _ { false }
                        }
                    }) { cx.okay_imports.insert(id, ()); }
                  }
                  _ { err = true; }
                }
            }
          }
          view_path_list(path, idents, id) {
            alt lookup_path_strict(cx, sc, path, ns_mod) {
              found(def) {
                cx.def_map.insert(id, def);
                for idents.each {|ident|
                    if mod_val_and_typ(mods, vals, typs, {|ns, lst|
                        alt cx.mod_scope(def).lookup(ident.node.name, ns) {
                          found(def) {
                            lst += [{ident: ident.node.name, def: def}];
                            true
                          }
                          _ { false }
                        }
                    }) { cx.okay_imports.insert(ident.node.id, ()); }
                }
              }
              _ { err = true; }
            }
          }
        }
        *resolving_now = false;
        if err { some(() as scope) }
        else { some({mods: mods, vals: vals, typs: typs} as scope) }
    })
}

enum glob_status { glob_todo, glob_disabled, glob_resolved(scope) }
type glob_info = @{pth: @view_path,
                   mut status: glob_status,
                   mut active: bool};
fn glob_info(pth: @view_path) -> glob_info {
    @{pth: pth, mut status: glob_todo, mut active: false}
}
fn glob_import_scope(cx: ctxt, sc: scopes, globs: [glob_info]) -> scope {
    fn resolve_glob(cx: ctxt, sc: scopes, info: glob_info) {
        info.status = glob_disabled;
        alt check info.pth.node {
          view_path_glob(pth, id) {
            alt lookup_path_strict(cx, sc, pth, ns_mod) {
              found(def) {
                cx.def_map.insert(id, def);
                info.status = glob_resolved(cx.mod_scope(def));
              }
              _ {}
            }
          }
        }
    }
    impl of scope for {cx: ctxt, sc: scopes, globs: [glob_info]} {
        fn lookup(i: ident, ns: ns) -> res {
            let mut cur = not_found, sp = none;
            for self.globs.each {|info|
                if info.active { cont; }
                info.active = true;
                if info.status == glob_todo {
                    resolve_glob(self.cx, self.sc, info);
                }
                alt info.status {
                  glob_resolved(scp) {
                    alt scp.lookup(i, ns) {
                      found(def) {
                        alt cur {
                          found(_) {
                            self.cx.err(info.pth.span, "ambiguous import: " +
                                        i + " is imported both from here");
                            self.cx.note(sp.get(), "and here");
                          }
                          _ { sp = some(info.pth.span); cur = found(def); }
                        }
                      }
                      _ {}
                    }
                  }
                  _ {}
                }
                info.active = false;
            }
            cur
        }
    }
    {cx: cx, sc: sc, globs: globs} as scope
}

// FIXME this is very crude and not terribly efficient. Intended as a
// stopgap until I implement the new pub/priv system (#1893)
fn export_scope(sc: scopes, m: _mod) -> scope {
    let mut saw_export = false;
    let mut names = [];
    for m.view_items.each {|vi|
        alt vi.node {
          view_item_export(vps) {
            saw_export = true;
            for vps.each {|vp|
                let (name, list) = alt check vp.node {
                  view_path_simple(id, _, _) { (id, none) }
                  view_path_list(pth, list, _) { (pth.idents[0], some(list)) }
                };
                names += [name];
                alt m.items.find {|i| i.ident == name} {
                  some(i) {
                    alt i.node {
                      item_enum(vs, _, _) {
                        for vs.each {|v|
                            if alt list {
                              none { true }
                              some(list) {
                                list.any {|i| v.node.name == i.node.name}
                              }
                            } { names += [v.node.name]; }
                        }
                      }
                      _ {}
                    }
                  }
                  _ {}
                }
            }
          }
          _ {}
        }
    }
    if !saw_export {
        for m.items.each {|i|
            names += [i.ident];
            alt i.node {
              item_enum(vs, _, _) {
                names += vec::map(vs, {|v| v.node.name});
              }
              _ {}
            }
        }
    }
    impl of scope for {sc: scopes, names: [ident]} {
        fn lookup(i: ident, ns: ns) -> res {
            if self.names.contains(i) {
                lookup_in_scopes_simple(self.sc, i, ns)
            } else { not_found }
        }
    }
    {sc: sc, names: names} as scope
}

// External modules lazily look up their values in the crate metadata
fn ext_mod_scope(cx: ctxt, id: def_id) -> scope {
    type mod_scope = @{path: [ident], id: def_id, cx: ctxt};
    impl of scope for mod_scope {
        fn lookup(i: ident, ns: ns) -> res {
            let key = {did: self.id, ns: ns, ident: i};
            alt self.cx.ext_map.find(key) {
              some(def) { ret found(def); }
              none {}
            }
            let mut res = not_found;
            for csearch::lookup_defs(self.cx.sess.cstore, self.id.crate,
                                     self.path + [i]).each {|d|
                let dns = ns_for_def(d);
                self.cx.ext_map.insert({did: self.id, ns: dns, ident: i}, d);
                if dns == ns { res = found(d); }
            }
            res
        }
    }

    let path = if id.node == ast::crate_node_id { [] }
               else { cstore::get_path(cx.sess.cstore, id) };
    let scp: mod_scope = @{path: path, id: id, cx: cx};
    scp as scope
}

enum top_scope { top_scope }
impl of scope for top_scope {
    fn lookup(i: ident, ns: ns) -> res {
        if ns == ns_typ {
            found(ast::def_prim_ty(alt i {
                "bool" { ast::ty_bool }
                "int" { ast::ty_int(ast::ty_i) }
                "uint" { ast::ty_uint(ast::ty_u) }
                "float" { ast::ty_float(ast::ty_f) }
                "str" { ast::ty_str }
                "char" { ast::ty_int(ast::ty_char) }
                "i8" { ast::ty_int(ast::ty_i8) }
                "i16" { ast::ty_int(ast::ty_i16) }
                "i32" { ast::ty_int(ast::ty_i32) }
                "i64" { ast::ty_int(ast::ty_i64) }
                "u8" { ast::ty_uint(ast::ty_u8) }
                "u16" { ast::ty_uint(ast::ty_u16) }
                "u32" { ast::ty_uint(ast::ty_u32) }
                "u64" { ast::ty_uint(ast::ty_u64) }
                "f32" { ast::ty_float(ast::ty_f32) }
                "f64" { ast::ty_float(ast::ty_f64) }
                _ { ret not_found; }
            }))
        } else { not_found }
    }
}

// Lookup utilities

fn lookup_path_strict(cx: ctxt, sc: scopes, p: @path, ns: ns) -> res {
    alt lookup_path(cx, sc, p, ns, true) {
      not_found {
        if !cx.reported.contains(p.idents.last()) {
            cx.reported += [p.idents.last()];
            let typ = alt ns {
              ns_val { "name" } ns_mod { "modulename" } ns_typ { "typename" }
            };
            cx.err(p.span, "unresolved " + typ + ": `" +
                   path_name(p) + "`");
        }
        not_found_err
      }
      r { r }
    }
}

fn lookup_path(cx: ctxt, sc: scopes, p: @path, ns: ns, check_capture: bool)
    -> res {
    let n_idents = p.idents.len();
    let sc = if p.global { cx.top_scope } else { sc };
    let top_ns = if n_idents == 1u { ns } else { ns_mod };
    let mut cur = if check_capture { 
        lookup_in_scopes(cx, p.span, sc, p.idents[0], top_ns)
    } else {
        lookup_in_scopes_simple(sc, p.idents[0], top_ns)
    };
    if n_idents == 1u { ret cur; }
    let mut i = 1u;
    while i < n_idents {
        let cur_mod = alt cur {
          found(def) { cx.mod_scope(def) }
          not_found {
            cx.err(p.span, "unresolved module " +
                   str::connect(p.idents.slice(0u, i), "::"));
            ret not_found_err;
          }
          not_found_err { ret not_found_err; }
        };
        let cur_ns = if i == n_idents - 1u { ns } else { ns_mod };
        cur = cur_mod.lookup(p.idents[i], cur_ns);
        i += 1u;
    }
    cur
}

fn lookup_in_scopes(cx: ctxt, sp: span, sc: scopes, i: ident, ns: ns) -> res {
    let mut closures_left = [], item_left = false, err = false;
    for list::each(sc) {|scp|
        alt scp {
          scope(scp) {
            alt scp.lookup(i, ns) {
              // FIXME check for bad use of typarams
              found(def) {
                let mut def = def;
                if def_is_local(def) {
                    if item_left {
                        cx.err(sp, if ns == ns_val {
                            "attempted dynamic environment-capture"
                        } else {
                            "attempt to use a type argument out of scope"
                        });
                    } else if ns == ns_val {
                        closures_left.riter {|id|
                            def = def_upvar(def_id_of_def(def).node,
                                            @def, id);
                        }
                    }
                }
                ret found(def);
              }
              not_found_err { err = true; }
              not_found {}
            }
          }
          bound_close(id) { closures_left += [id]; }
          bound_item { item_left = true; }
        }
    }
    if err { not_found_err } else { not_found }
}

// Only suitable for item-level scopes. Simpler and faster, and
// guaranteed not to emit errors (which is useful when probing for
// variant names)
fn lookup_in_scopes_simple(sc: scopes, i: ident, ns: ns) -> res {
    let mut err = false;
    for list::each(sc) {|scp|
        alt scp {
          scope(scp) {
            alt scp.lookup(i, ns) {
              r@found(_) { ret r; }
              not_found_err { err = true; }
              not_found {}
            }
          }
          _ {}
        }
    }
    if err { not_found_err } else { not_found }
}

// Building up the scope graph

fn add_path(cx: ctxt, id: node_id, pth: @path, sc: scopes, ns: ns) {
    cx.paths += [{id: id, sc: sc, pth: pth, ns: ns}];
}

type vt = visit::vt<scopes>;

// Builds the scope objects for the AST (some unresolved, which are
// stored in cx.fixup), and stores an entry for each path in cx.paths.
fn build_scopes(cx: ctxt, crate: @crate) {
    visit::visit_crate(*crate, ext(@nil, top_scope as scope), visit::mk_vt(@{
        visit_expr: {|e: @expr, sc, v|
            alt e.node {
              expr_path(p) {
                add_path(cx, e.id, p, sc, ns_val);
              }
              expr_fn(_, _, _, cs) | expr_fn_block(_, _, cs) {
                for (*cs).each {|c|
                    let pt = ast_util::ident_to_path(c.span, c.name);
                    add_path(cx, c.id, pt, sc, ns_val);
                }
              }
              _ {}
            }
            alt e.node {
              expr_fn_block(*) | expr_fn(*) {
                visit::visit_expr(e, @cons(bound_close(e.id), sc), v);
              }
              _ { visit::visit_expr(e, sc, v); }
            }
        },
        visit_item: {|i, sc, v|
            build_for_item(cx, i, @cons(bound_item, sc), v);
        },
        visit_mod: {|m, _s, id, sc, v| build_for_mod(cx, m, id, sc, v)},
        visit_arm: {|a: arm, sc, v: vt|
            for a.pats.each {|p| v.visit_pat(p, sc, v); }
            let sc = ext(sc, pat_scope(cx, sc, a.pats[0], binding));
            for a.pats.eachi {|i, p|
                if i > 0u {
                    let fin = {|| resolve_pat(cx, sc, p, binding); none };
                    cx.fixups += [@{mut done: none, finish_fn: fin}];
                }
            }
            visit::visit_expr_opt(a.guard, sc, v);
            v.visit_block(a.body, sc, v);
        },
        visit_ty_params: {|_tps, _sc, _v|},
        visit_ty: {|ty: @ty, sc, v|
            alt ty.node {
              ty_path(p, id) { add_path(cx, id, p, sc, ns_typ); }
              _ {}
            }
            visit::visit_ty(ty, sc, v);
        },
        visit_fn: {|kind: visit::fn_kind, decl: fn_decl, blk, sp, id, sc, v|
            let sc = alt check kind {
              visit::fk_item_fn(_, tps) |
              visit::fk_res(_, tps, _) | visit::fk_ctor(_, tps, _, _) {
                build_for_tps(sc, tps, 0u, v)
              }
              visit::fk_anon(*) | visit::fk_fn_block(*) { sc }
            };
            let sc = ext(sc, arg_scope(decl));
            visit::visit_fn(kind, decl, blk, sp, id, sc, v);
        },
        visit_block: {|blk: blk, sc, v: vt|
            let items = blk.node.stmts.filter_map {|s|
                alt s.node {
                  stmt_decl(@{node: decl_item(i), _}, _) { some(i) }
                  _ { none }
                }
            };
            let mut sc = extend_for_items(cx, items, blk.node.view_items, sc);
            for blk.node.stmts.each {|s|
                alt s.node {
                  stmt_decl(@{node: decl_item(i), _}, _) {
                    v.visit_item(i, sc, v);
                  }
                  stmt_decl(@{node: decl_local(locs), _}, _) {
                    sc = build_for_locals(cx, locs, sc, v);
                  }
                  stmt_expr(ex, _) | stmt_semi(ex, _) {
                    v.visit_expr(ex, sc, v);
                  }
                }
            }
            visit::visit_expr_opt(blk.node.expr, sc, v);
        },
        visit_constr: {|p, _sp, id, sc, _v|
            add_path(cx, id, p, sc, ns_val);
        }
        with *visit::default_visitor()
    }));
}

fn build_for_tps(sc: scopes, tps: [ty_param], off: uint, v: vt) -> scopes {
    let mut sc = sc;
    for tps.eachi {|n, tp|
        for vec::each(*tp.bounds) {|bound|
            alt bound {
              bound_iface(t) { v.visit_ty(t, sc, v); }
              bound_copy | bound_send | bound_const { }
            }
        }
        let def = def_ty_param(local_def(tp.id), n + off);
        sc = ext(sc, single_def(tp.ident, def, ns_typ));
    }
    sc
}

fn build_for_item(cx: ctxt, i: @item, sc: scopes, v: vt) {
    alt i.node {
      item_enum(_, tps, _) | item_ty(_, tps, _) {
        let sc = build_for_tps(sc, tps, 0u, v);
        visit::visit_item(i, sc, v);
      }
      item_impl(tps, _, ifce, sty, methods) {
        let sc = build_for_tps(sc, tps, 0u, v);
        for ifce.each {|p|
            add_path(cx, p.id, p.path, sc, ns_typ);
            visit::visit_path(p.path, sc, v)
        }
        v.visit_ty(sty, sc, v);
        let n = tps.len();
        for methods.each {|m|
            let sc = build_for_tps(sc, m.tps, n, v);
            let slf = single_def("self", def_self(m.self_id), ns_val);
            let sc = ext(ext(sc ,slf), arg_scope(m.decl));
            visit::visit_fn(visit::fk_method(m.ident, m.tps, m),
                            m.decl, m.body, m.span, m.id, sc, v);
        }
      }
      item_iface(tps, _, ms) {
        let sc = ext(build_for_tps(sc, tps, 0u, v),
                     single_def("self", def_self(i.id), ns_typ));
        let n = tps.len();
        for ms.each {|m|
            let m_sc = build_for_tps(sc, m.tps, n, v);
            for m.decl.inputs.each {|a| v.visit_ty(a.ty, m_sc, v);}
            v.visit_ty(m.decl.output, m_sc, v);
        }
      }
      item_class(tps, _, _, _, _, _) {
        let sc = build_for_tps(sc, tps, 0u, v);
        // FIXME propagate tp offsets
        visit::visit_item(i, sc, v);
      }
      item_mod(m) {
        build_for_mod(cx, m, i.id, sc, v);
      }
      item_native_mod(m) {
        let lst = m.items.map {|ni|
            alt ni.node {
              native_item_fn(decl, tps) {
                let f_sc = build_for_tps(sc, tps, 0u, v);
                v.visit_native_item(ni, f_sc, v);
                {ident: ni.ident, def: def_fn(local_def(ni.id), decl.purity)}
              }
            }
        };
        cx.mod_map.insert(local_def(i.id), multi_def(lst, ns_val));
      }
      item_res(*) | item_fn(*) | item_const(*) {
        visit::visit_item(i, sc, v);
      }
    }
}

fn extend_for_items(cx: ctxt, is: [@item], vis: [@view_item], sc: scopes)
    -> scopes {
    let item_scope = scope_for_items(is);
    let mut isc = ext(sc, item_scope), globs = [], imports = [];
    for vis.each {|vi|
        alt vi.node {
          view_item_import(ps) {
            for ps.each {|p|
                alt p.node {
                  view_path_simple(*) | view_path_list(*) {
                    let local_glob_sc = if globs.len() > 0u {
                        ext(isc, glob_import_scope(cx, isc, globs))
                    } else { isc };
                    let imp = import_scope(cx, local_glob_sc, p);
                    imports += [imp];
                    isc = ext(isc, imp);
                  }
                  view_path_glob(*) {
                    globs += [glob_info(p)];
                  }
                }
            }
          }
          view_item_use(nm, _, id) {
            alt cstore::find_use_stmt_cnum(cx.sess.cstore, id) {
              some(cnum) {
                let def = def_mod({crate: cnum, node: ast::crate_node_id});
                let us = single_def(nm, def, ns_mod);
                imports += [us];
                isc = ext(isc, us);
              }
              none {}
            }
          }
          view_item_export(_) {}
        }
    }
    let mut sc = sc;
    if globs.len() > 0u { sc = ext(sc, glob_import_scope(cx, isc, globs)); }
    for imports.each {|scp| sc = ext(sc, scp); }
    ext(sc, item_scope)
}

fn scope_for_items(is: [@item]) -> scope {
    let mut mods = [], vals = [], typs = [];
    fn add(&lst: deflist, i: ident, def: def) {
        lst += [{ident: i, def: def}];
    }
    for is.each {|i|
        let id = local_def(i.id);
        alt i.node {
          item_const(_, _) { add(vals, i.ident, def_const(id)); }
          item_fn(d, _, _) { add(vals, i.ident, def_fn(id, d.purity)); }
          item_mod(_) { add(mods, i.ident, def_mod(id)); }
          item_native_mod(_) { add(mods, i.ident, def_native_mod(id)); }
          // FIXME classes are more complicated
          item_ty(*) | item_class(*) | item_iface(*) {
            add(typs, i.ident, def_ty(id));
          }
          item_enum(vs, _, _) {
            add(typs, i.ident, def_ty(id));
            for vs.each {|v|
                add(vals, v.node.name, def_variant(id, local_def(v.node.id)));
            }
          }
          item_res(_, _, _, _, cid, _) {
            add(typs, i.ident, def_ty(id));
            add(vals, i.ident, def_fn(local_def(cid), impure_fn));
          }
          item_impl(*) {}
        }
    }
    {mods: mods, vals: vals, typs: typs} as scope
}

fn build_for_locals(cx: ctxt, locs: [@local], sc: scopes, v: vt) -> scopes {
    let mut sc = sc;
    for locs.each {|loc|
        visit::visit_local(loc, sc, v);
        sc = ext(sc, pat_scope(cx, sc, loc.node.pat,
                               local(loc.node.is_mutbl)));
    }
    sc
}

fn build_for_mod(cx: ctxt, m: _mod, id: node_id, sc: scopes, v: vt) {
    let sc = extend_for_items(cx, m.items, m.view_items, sc);
    cx.mod_map.insert(local_def(id), export_scope(sc, m));
    for m.items.each {|i| v.visit_item(i, sc, v);}
}

fn resolve_paths(cx: ctxt) {
    let mut paths = [];
    cx.paths <-> paths;
    for paths.each {|info|
        alt lookup_path_strict(cx, info.sc, info.pth, info.ns) {
          found(def) { cx.def_map.insert(info.id, def); }
          _ {}
        }
    }
}

// Impl resolution

type method_info = {did: def_id, n_tps: uint, ident: ast::ident};
/* what are the did and ident here? */
/* ident = the name of the impl */
type _impl = {did: def_id, ident: ast::ident, methods: [@method_info]};

type iscope = @[@_impl];
type iscopes = @list::list<iscope>;

type ivt = visit::vt<iscopes>;

fn resolve_impls(cx: ctxt, crate: @crate) {
    // First a pass that collects iscopes_ lists for each mod and each
    // expr that needs an iscope.
    visit::visit_crate(*crate, @nil, visit::mk_vt(@{
        visit_expr: {|e: @expr, sc, v|
            alt e.node {
              // Store the visible impls in all exprs that might need them
              ast::expr_field(_, _, _) | ast::expr_path(_) |
              ast::expr_cast(_, _) | ast::expr_binary(_, _, _) |
              ast::expr_unary(_, _) | ast::expr_assign_op(_, _, _) |
              ast::expr_index(_, _) { cx.impl_map.insert(e.id, sc); }
              ast::expr_new(p, _, _) { cx.impl_map.insert(p.id, sc); }
              _ {}
            }
            visit::visit_expr(e, sc, v);
        },
        visit_mod: {|m, span, id, sc, v|
            let mut impls = [];
            for m.view_items.each {|vi|
                add_impls_for_view_item(cx, vi, impls, sc);
            }
            for m.items.each {|i| add_impls_for_item(i, impls);}
            let sc = if impls.len() > 0u { @cons(@impls, sc) } else { sc };
            visit::visit_mod(m, span, id, sc, v);
            cx.impl_map.insert(id, @cons(impls_for_mod(cx, local_def(id)),
                                         @nil));

        },
        visit_block: {|blk, sc, v|
            let mut impls = [];
            for blk.node.view_items.each {|vi|
                add_impls_for_view_item(cx, vi, impls, sc);
            }
            for blk.node.stmts.each {|s|
                alt s.node {
                  stmt_decl(@{node: decl_item(i), _}, _) {
                    add_impls_for_item(i, impls);
                  }
                  _ {}
                }
            }
            let sc = if impls.len() > 0u { @cons(@impls, sc) } else { sc };
            visit::visit_block(blk, sc, v);
        },
        visit_view_item: {|vi, _sc, _v|
            fn chk(cx: ctxt, sp: span, id: node_id) {
                if !cx.okay_imports.contains_key(id) {
                    cx.err(sp, "unresolved import");
                }
            }
            alt vi.node {
              view_item_import(vps) {
                for vps.each {|vp|
                    alt vp.node {
                      view_path_simple(_, _, id) {
                        if cx.def_map.contains_key(id) {
                            chk(cx, vp.span, id);
                        }
                      }
                      view_path_list(_, ids, id) {
                        if cx.def_map.contains_key(id) {
                            for ids.each {|id| chk(cx, id.span, id.node.id);}
                        }
                      }
                      _ {}
                    }
                }
              }
              _ {}
            }
        }
        with *visit::default_visitor()
    }));
}

fn add_impls_for_view_item(cx: ctxt, vi: @view_item, &impls: [@_impl],
                           sc: iscopes) {
    alt vi.node {
      view_item_import(vps) {
        for vps.each {|vp|
            let id = alt vp.node {
              view_path_simple(_, _, id) | view_path_list(_, _, id) |
              view_path_glob(_, id) { id }
            };
            let mod_impls = alt check cx.def_map.find(id) {
              some(def_mod(id)) | some(def_native_mod(id)) {
                some(impls_for_mod(cx, id))
              }
              none { none }
            };
            alt vp.node {
              view_path_simple(ident, pth, id) {
                let impl_name = vec::last(pth.idents);
                let renamed = ident != impl_name;
                let mut fnd = false;
                if pth.idents.len() == 1u {
                    for list::each(sc) {|is|
                        for (*is).each {|im|
                            if im.ident == impl_name {
                                fnd = true;
                                impls += [@{ident: ident with *im}];
                            }
                        }
                        if fnd { break; }
                    }
                } else {
                    mod_impls.iter {|is|
                        for (*is).each {|im|
                            if im.ident == impl_name {
                                fnd = true;
                                if renamed {
                                    impls += [@{ident: ident with *im}];
                                } else { impls += [im]; }
                            }
                        }
                    }
                }
                if fnd { cx.okay_imports.insert(id, ()); }
              }
              view_path_list(pth, idents, _) {
                mod_impls.iter {|is|
                    for (*is).each {|im|
                        alt idents.find {|idnt| idnt.node.name == im.ident} {
                          some(ident) {
                            cx.okay_imports.insert(ident.node.id, ());
                            impls += [im];
                          }
                          none {}
                        }
                    }
                }
              }
              view_path_glob(pth, _) {
                mod_impls.iter {|is| impls += *is;}
              }
            }
        }
      }
      _ {}
    }
}

fn add_impls_for_item(i: @item, &impls: [@_impl]) {
    fn mth_info(&&m: @method) -> @method_info {
        @{did: local_def(m.id),
          n_tps: vec::len(m.tps),
          ident: m.ident}
    }
    alt i.node {
      ast::item_impl(_, _, _, _, mthds) {
        impls += [@{did: local_def(i.id),
                    ident: i.ident,
                    methods: vec::map(mthds, mth_info)}];
      }
      ast::item_class(_, ifces, items, _, _, _) {
          let (_, mthds) = ast_util::split_class_items(items);
          vec::iter(ifces) {|p|
              impls += [@{did: local_def(p.id),
                          ident: i.ident,
                          methods: vec::map(mthds, mth_info)}];
          }
      }
      _ {}
    }
}

fn impls_for_mod(cx: ctxt, id: def_id) -> iscope {
    alt cx.iscope_per_mod.find(id) {
      some(some(scs)) { ret scs; }
      some(none) { ret @[]; }
      none {}
    }
    cx.iscope_per_mod.insert(id, none);
    let scs = if id.crate == local_crate {
        let md = if id.node == crate_node_id {
            cx.crate.node.module
        } else {
            alt check cx.ast_map.get(id.node) {
              ast_map::node_item(i, _) {
                alt check i.node {
                  item_mod(m) { m }
                  item_native_mod(_) { ret @[]; }
                }
              }
            }
        };
        let mut impls = [];
        for md.view_items.each {|vi|
            add_impls_for_view_item(cx, vi, impls, @nil);
        }
        impls = impls.filter {|im| ast_util::is_exported(im.ident, md)};
        for md.items.each {|i|
            if ast_util::is_exported(i.ident, md) {
                add_impls_for_item(i, impls);
            }
        }
        @impls
    } else {
        csearch::get_impls_for_mod(cx.sess.cstore, id, none)
    };
    cx.iscope_per_mod.insert(id, some(scs));
    scs
}
