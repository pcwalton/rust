// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Prune things that are private


use extract;
use syntax::ast;
use syntax::ast_map;
use astsrv;
use doc;
use fold::Fold;
use fold;
use pass::Pass;

use std::util;

pub struct PrunePrivatePass;

pub fn mk_pass() -> @Pass {
    @PrunePrivatePass as @Pass
}

impl Pass for PrunePrivatePass {
    fn name(&self) -> ~str {
        ~"prune_private"
    }

    fn run(&self, srv: astsrv::Srv, doc: doc::Doc) -> doc::Doc {
        // First strip private methods out of impls
        let fold = PrivateMethodPruner {
            srv: srv.clone(),
        };
        let doc = fold.fold_doc(doc);

        // Then strip private items and empty impls
        let fold = PrivateItemPruner {
            srv: srv,
        };
        fold.fold_doc(doc)
    }
}

struct PrivateMethodPruner {
    srv: astsrv::Srv,
}

impl Fold for PrivateMethodPruner {
    fn fold_impl(&self, doc: doc::ImplDoc) -> doc::ImplDoc {
        let doc = fold::default_fold_impl(self, doc);

        do astsrv::exec(self.srv.clone()) |ctxt| {
            match ctxt.ast_map.get_copy(&doc.item.id) {
                ast_map::node_item(item, _) => {
                    match item.node {
                        ast::item_impl(_, None, _, ref methods) => {
                            // Associated impls have complex rules for method visibility
                            strip_priv_methods(doc.clone(), *methods, item.vis)
                        }
                        ast::item_impl(_, Some(_), _ ,_) => {
                            // Trait impls don't
                            doc.clone()
                        }
                        _ => fail!()
                    }
                }
                _ => fail!()
            }
        }
    }
}

fn strip_priv_methods(
    doc: doc::ImplDoc,
    methods: &[@ast::method],
    item_vis: ast::visibility
) -> doc::ImplDoc {
    let methods = do doc.methods.iter().filter |method| {
        let ast_method = do methods.iter().find |m| {
            extract::to_str(m.ident) == method.name
        };
        assert!(ast_method.is_some());
        let ast_method = ast_method.unwrap();
        match ast_method.vis {
            ast::public => true,
            ast::private => false,
            ast::inherited => item_vis == ast::public
        }
    }.map(|x| (*x).clone()).collect();

    doc::ImplDoc {
        methods: methods,
        .. doc
    }
}

struct PrivateItemPruner {
    srv: astsrv::Srv,
}

impl Fold for PrivateItemPruner {
    fn fold_mod(&self, doc: doc::ModDoc) -> doc::ModDoc {
        let doc = fold::default_fold_mod(self, doc);

        doc::ModDoc {
            items: doc.items.iter().filter(|item_tag| {
                match item_tag {
                    & &doc::ImplTag(ref doc) => {
                        if doc.trait_types.is_empty() {
                            // This is an associated impl. We have already pruned the
                            // non-visible methods. If there are any left then
                            // retain the impl, otherwise throw it away
                            !doc.methods.is_empty()
                        } else {
                            // This is a trait implementation, make it visible
                            // NB: This is not quite right since this could be an impl
                            // of a private trait. We can't know that without running
                            // resolve though.
                            true
                        }
                    }
                    _ => {
                        is_visible(self.srv.clone(), item_tag.item())
                    }
                }
            }).map(|x| (*x).clone()).collect(),
            .. doc
        }
    }
}

fn is_visible(srv: astsrv::Srv, doc: doc::ItemDoc) -> bool {
    let id = doc.id;

    do astsrv::exec(srv) |ctxt| {
        match ctxt.ast_map.get_copy(&id) {
            ast_map::node_item(item, _) => {
                match &item.node {
                    &ast::item_impl(*) => {
                        // Impls handled elsewhere
                        fail!()
                    }
                    _ => {
                        // Otherwise just look at the visibility
                        item.vis == ast::public
                    }
                }
            }
            _ => util::unreachable()
        }
    }
}


#[cfg(test)]
mod test {
    use astsrv;
    use doc;
    use extract;
    use pass::Pass;
    use tystr_pass::TyStrPass;
    use prune_private_pass::PrunePrivatePass;

    fn mk_doc(source: ~str) -> doc::Doc {
        do astsrv::from_str(source.clone()) |srv| {
            let doc = extract::from_srv(srv.clone(), ~"");
            let doc = TyStrPass.run(srv.clone(), doc);
            PrunePrivatePass.run(srv.clone(), doc)
        }
    }

    #[test]
    fn should_prune_items_without_pub_modifier() {
        let doc = mk_doc(~"mod a { }");
        assert!(doc.cratemod().mods().is_empty());
    }

    #[test]
    fn should_not_prune_trait_impls() {
        // Impls are more complicated
        let doc = mk_doc(
            ~" \
              trait Foo { } \
              impl Foo for int { } \
              ");
        assert!(!doc.cratemod().impls().is_empty());
    }

    #[test]
    fn should_prune_associated_methods_without_vis_modifier_on_impls_without_vis_modifier() {
        let doc = mk_doc(
            ~"impl Foo {\
              pub fn bar() { }\
              fn baz() { }\
              }");
        assert_eq!(doc.cratemod().impls()[0].methods.len(), 1);
    }

    #[test]
    fn should_prune_priv_associated_methods_on_impls_without_vis_modifier() {
        let doc = mk_doc(
            ~"impl Foo {\
              pub fn bar() { }\
              fn baz() { }\
              }");
        assert_eq!(doc.cratemod().impls()[0].methods.len(), 1);
    }

    #[test]
    fn should_prune_priv_associated_methods_on_pub_impls() {
        let doc = mk_doc(
            ~"impl Foo {\
              pub fn bar() { }\
              fn baz() { }\
              }");
        assert_eq!(doc.cratemod().impls()[0].methods.len(), 1);
    }

    #[test]
    fn should_prune_associated_methods_without_vis_modifier_on_priv_impls() {
        let doc = mk_doc(
            ~"impl Foo {\
              pub fn bar() { }\
              fn baz() { }\
              }");
        assert_eq!(doc.cratemod().impls()[0].methods.len(), 1);
    }

    #[test]
    fn should_prune_priv_associated_methods_on_priv_impls() {
        let doc = mk_doc(
            ~"impl Foo {\
              pub fn bar() { }\
              fn baz() { }\
              }");
        assert_eq!(doc.cratemod().impls()[0].methods.len(), 1);
    }

    #[test]
    fn should_prune_associated_impls_with_no_pub_methods() {
        let doc = mk_doc(
            ~"impl Foo {\
              fn baz() { }\
              }");
        assert!(doc.cratemod().impls().is_empty());
    }

    #[test]
    fn should_not_prune_associated_impls_with_pub_methods() {
        let doc = mk_doc(
            ~" \
              impl Foo { pub fn bar() { } } \
              ");
        assert!(!doc.cratemod().impls().is_empty());
    }
}
