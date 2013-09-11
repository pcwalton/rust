// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
Divides the document tree into pages.

Each page corresponds is a logical section. There may be pages for
individual modules, pages for the crate, indexes, etc.
*/


use astsrv;
use config;
use doc::ItemUtils;
use doc;
use fold::Fold;
use fold;
use pass::Pass;

use std::comm::*;
use std::task;
use syntax::ast;

#[cfg(test)] use doc::PageUtils;

struct PagePass {
    output_style: config::OutputStyle,
}

pub fn mk_pass(output_style: config::OutputStyle) -> @Pass {
    @PagePass {
        output_style: output_style,
    } as @Pass
}

impl Pass for PagePass {
    fn name(&self) -> ~str {
        ~"page"
    }

    fn run(&self, _: astsrv::Srv, doc: doc::Doc) -> doc::Doc {
        if self.output_style == config::DocPerCrate {
            return doc
        }

        let (result_port, result_chan) = stream();
        let (page_port, page_chan) = stream();
        let page_chan = SharedChan::new(page_chan);
        do task::spawn {
            result_chan.send(make_doc_from_pages(&page_port));
        };

        find_pages(doc, page_chan);
        result_port.recv()
    }
}

type PagePort = Port<Option<doc::Page>>;
type PageChan = SharedChan<Option<doc::Page>>;

fn make_doc_from_pages(page_port: &PagePort) -> doc::Doc {
    let mut pages = ~[];
    loop {
        let val = page_port.recv();
        if val.is_some() {
            pages.push(val.unwrap());
        } else {
            break;
        }
    }
    doc::Doc {
        pages: pages
    }
}

fn find_pages(doc: doc::Doc, page_chan: PageChan) {
    let fold = PageFold {
        page_chan: page_chan.clone(),
    };
    fold.fold_doc(doc.clone());

    page_chan.send(None);
}

struct PageFold {
    page_chan: PageChan,
}

impl Fold for PageFold {
    fn fold_crate(&self, doc: doc::CrateDoc) -> doc::CrateDoc {
        let doc = fold::default_fold_crate(self, doc);

        let page = doc::CratePage(doc::CrateDoc {
            topmod: strip_mod(doc.topmod.clone()),
            .. doc.clone()
        });

        self.page_chan.send(Some(page));

        doc
    }

    fn fold_mod(&self, doc: doc::ModDoc) -> doc::ModDoc {
        let doc = fold::default_fold_mod(self, doc);

        if doc.id() != ast::CRATE_NODE_ID {
            let doc = strip_mod(doc.clone());
            let page = doc::ItemPage(doc::ModTag(doc));
            self.page_chan.send(Some(page));
        }

        doc
    }

    fn fold_nmod(&self, doc: doc::NmodDoc) -> doc::NmodDoc {
        let doc = fold::default_fold_nmod(self, doc);
        let page = doc::ItemPage(doc::NmodTag(doc.clone()));
        self.page_chan.send(Some(page));
        return doc;
    }
}

fn strip_mod(doc: doc::ModDoc) -> doc::ModDoc {
    doc::ModDoc {
        items: do doc.items.iter().filter |item| {
            match **item {
              doc::ModTag(_) | doc::NmodTag(_) => false,
              _ => true
            }
        }.map(|x| (*x).clone()).collect::<~[doc::ItemTag]>(),
        .. doc.clone()
    }
}

#[cfg(test)]
mod test {
    use astsrv;
    use config;
    use attr_pass;
    use doc;
    use extract;
    use prune_hidden_pass;
    use page_pass::run;

    fn mk_doc_(
        output_style: config::OutputStyle,
        source: ~str
    ) -> doc::Doc {
        do astsrv::from_str(source.clone()) |srv| {
            let doc = extract::from_srv(srv.clone(), ~"");
            let doc = (attr_pass::mk_pass().f)(srv.clone(), doc);
            let doc = (prune_hidden_pass::mk_pass().f)(srv.clone(), doc);
            run(srv.clone(), doc, output_style)
        }
    }

    fn mk_doc(source: ~str) -> doc::Doc {
        mk_doc_(config::DocPerMod, source.clone())
    }

    #[test]
    fn should_not_split_the_doc_into_pages_for_doc_per_crate() {
        let doc = mk_doc_(
            config::DocPerCrate,
            ~"mod a { } mod b { mod c { } }"
        );
        assert_eq!(doc.pages.len(), 1u);
    }

    #[test]
    fn should_make_a_page_for_every_mod() {
        let doc = mk_doc(~"mod a { }");
        // hidden __std_macros module at the start.
        assert_eq!(doc.pages.mods()[0].name_(), ~"a");
    }

    #[test]
    fn should_remove_mods_from_containing_mods() {
        let doc = mk_doc(~"mod a { }");
        assert!(doc.cratemod().mods().is_empty());
    }
}
