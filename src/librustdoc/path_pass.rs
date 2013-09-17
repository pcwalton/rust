// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Records the full path to items


use astsrv;
use doc::ItemUtils;
use doc;
use fold::Fold;
use fold;
use pass::Pass;

#[cfg(test)] use extract;

use syntax::ast;

struct PathPass;

pub fn mk_pass() -> @Pass {
    @PathPass as @Pass
}

struct Ctxt {
    srv: astsrv::Srv,
    path: @mut ~[~str]
}

impl Clone for Ctxt {
    fn clone(&self) -> Ctxt {
        Ctxt {
            srv: self.srv.clone(),
            path: @mut (*self.path).clone()
        }
    }
}

impl Pass for PathPass {
    fn name(&self) -> ~str {
        ~"path"
    }

    fn run(&self, srv: astsrv::Srv, doc: doc::Doc) -> doc::Doc {
        let ctxt = Ctxt {
            srv: srv,
            path: @mut ~[]
        };
        ctxt.fold_doc(doc)
    }
}

impl Fold for Ctxt {
    fn fold_item(&self, doc: doc::ItemDoc) -> doc::ItemDoc {
        doc::ItemDoc {
            path: (*self.path).clone(),
            .. doc
        }
    }

    fn fold_mod(&self, doc: doc::ModDoc) -> doc::ModDoc {
        let is_topmod = doc.id() == ast::CRATE_NODE_ID;

        if !is_topmod {
            self.path.push(doc.name_());
        }
        let doc = fold::default_fold_mod(self, doc);
        if !is_topmod {
            self.path.pop();
        }

        doc::ModDoc {
            item: self.fold_item(doc.item.clone()),
            .. doc
        }
    }

    fn fold_nmod(&self, doc: doc::NmodDoc) -> doc::NmodDoc {
        self.path.push(doc.name_());
        let doc = fold::default_fold_nmod(self, doc);
        self.path.pop();

        doc::NmodDoc {
            item: self.fold_item(doc.item.clone()),
            .. doc
        }
    }
}

#[test]
fn should_record_mod_paths() {
    let source = ~"mod a { mod b { mod c { } } mod d { mod e { } } }";
    do astsrv::from_str(source) |srv| {
        let doc = extract::from_srv(srv.clone(), ~"");
        let doc = PathPass.run(srv.clone(), doc);
        // hidden __std_macros module at the start.
        assert_eq!(doc.cratemod().mods()[1].mods()[0].mods()[0].path(),
                   ~[~"a", ~"b"]);
        assert_eq!(doc.cratemod().mods()[1].mods()[1].mods()[0].path(),
                   ~[~"a", ~"d"]);
    }
}

#[test]
fn should_record_fn_paths() {
    let source = ~"mod a { fn b() { } }";
    do astsrv::from_str(source) |srv| {
        let doc = extract::from_srv(srv.clone(), ~"");
        let doc = PathPass.run(srv.clone(), doc);
        // hidden __std_macros module at the start.
        assert_eq!(doc.cratemod().mods()[1].fns()[0].path(), ~[~"a"]);
    }
}
