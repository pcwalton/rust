// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use doc;
#[cfg(test)] use extract;
#[cfg(test)] use parse;

pub trait Fold {
    fn fold_ItemTag(&self, doc: doc::ItemTag) -> doc::ItemTag {
        match doc {
            doc::ModTag(ModDoc) => doc::ModTag(self.fold_mod(ModDoc)),
            doc::NmodTag(nModDoc) => doc::NmodTag(self.fold_nmod(nModDoc)),
            doc::FnTag(FnDoc) => doc::FnTag(self.fold_fn(FnDoc)),
            doc::StaticTag(StaticDoc) => {
                doc::StaticTag(self.fold_static(StaticDoc))
            }
            doc::EnumTag(EnumDoc) => doc::EnumTag(self.fold_enum(EnumDoc)),
            doc::TraitTag(TraitDoc) => {
                doc::TraitTag(self.fold_trait(TraitDoc))
            }
            doc::ImplTag(ImplDoc) => doc::ImplTag(self.fold_impl(ImplDoc)),
            doc::TyTag(TyDoc) => doc::TyTag(self.fold_type(TyDoc)),
            doc::StructTag(StructDoc) => {
                doc::StructTag(self.fold_struct(StructDoc))
            }
        }
    }

    fn fold_doc(&self, doc: doc::Doc) -> doc::Doc {
        doc::Doc {
            pages: do doc.pages.iter().map |page| {
                match (*page).clone() {
                    doc::CratePage(doc) => {
                        doc::CratePage(self.fold_crate(doc))
                    }
                    doc::ItemPage(doc) => {
                        doc::ItemPage(self.fold_ItemTag(doc))
                    }
                }
            }.collect(),
            .. doc
        }
    }

    fn fold_crate(&self, doc: doc::CrateDoc) -> doc::CrateDoc {
        default_fold_crate(self, doc)
    }

    fn fold_item(&self, doc: doc::ItemDoc) -> doc::ItemDoc {
        doc
    }

    fn fold_mod(&self, doc: doc::ModDoc) -> doc::ModDoc {
        default_fold_mod(self, doc)
    }

    fn fold_nmod(&self, doc: doc::NmodDoc) -> doc::NmodDoc {
        default_fold_nmod(self, doc)
    }

    fn fold_fn(&self, doc: doc::FnDoc) -> doc::FnDoc {
        doc::SimpleItemDoc {
            item: self.fold_item(doc.item.clone()),
            .. doc
        }
    }

    fn fold_static(&self, doc: doc::StaticDoc) -> doc::StaticDoc {
        doc::SimpleItemDoc {
            item: self.fold_item(doc.item.clone()),
            .. doc
        }
    }

    fn fold_enum(&self, doc: doc::EnumDoc) -> doc::EnumDoc {
        default_fold_enum(self, doc)
    }

    fn fold_trait(&self, doc: doc::TraitDoc) -> doc::TraitDoc {
        default_fold_trait(self, doc)
    }

    fn fold_impl(&self, doc: doc::ImplDoc) -> doc::ImplDoc {
        default_fold_impl(self, doc)
    }

    fn fold_type(&self, doc: doc::TyDoc) -> doc::TyDoc {
        doc::SimpleItemDoc {
            item: self.fold_item(doc.item.clone()),
            .. doc
        }
    }

    fn fold_struct(&self, doc: doc::StructDoc) -> doc::StructDoc {
        doc::StructDoc {
            item: self.fold_item(doc.item.clone()),
            .. doc
        }
    }
}

pub fn default_fold_crate<T:Fold>(this: &T, doc: doc::CrateDoc)
                                  -> doc::CrateDoc {
    doc::CrateDoc {
        topmod: this.fold_mod(doc.topmod.clone())
    }
}

pub fn default_fold_mod<T:Fold>(this: &T, doc: doc::ModDoc) -> doc::ModDoc {
    doc::ModDoc {
        item: this.fold_item(doc.item.clone()),
        items: doc.items.iter().map(|ItemTag| {
            this.fold_ItemTag((*ItemTag).clone())
        }).collect(),
        .. doc
    }
}

pub fn default_fold_nmod<T:Fold>(this: &T, doc: doc::NmodDoc)
                                 -> doc::NmodDoc {
    doc::NmodDoc {
        item: this.fold_item(doc.item.clone()),
        fns: doc.fns.iter().map(|FnDoc| {
            this.fold_fn((*FnDoc).clone())
        }).collect(),
        .. doc
    }
}

pub fn default_fold_enum<T:Fold>(this: &T, doc: doc::EnumDoc)
                                 -> doc::EnumDoc {
    doc::EnumDoc {
        item: this.fold_item(doc.item.clone()),
        .. doc
    }
}

pub fn default_fold_trait<T:Fold>(this: &T, doc: doc::TraitDoc)
                                  -> doc::TraitDoc {
    doc::TraitDoc {
        item: this.fold_item(doc.item.clone()),
        .. doc
    }
}

pub fn default_fold_impl<T:Fold>(this: &T, doc: doc::ImplDoc)
                                 -> doc::ImplDoc {
    doc::ImplDoc {
        item: this.fold_item(doc.item.clone()),
        .. doc
    }
}

struct DefaultFold;

impl Fold for DefaultFold {}

#[test]
fn default_fold_should_produce_same_doc() {
    let source = @"mod a { fn b() { } mod c { fn d() { } } }";
    let ast = parse::from_str(source);
    let doc = extract::extract(ast, ~"");
    let fld = DefaultFold;
    let folded = fld.fold_doc(doc.clone());
    assert_eq!(doc, folded);
}

#[test]
fn default_fold_should_produce_same_statics() {
    let source = @"static a: int = 0;";
    let ast = parse::from_str(source);
    let doc = extract::extract(ast, ~"");
    let fld = DefaultFold;
    let folded = fld.fold_doc(doc.clone());
    assert_eq!(doc, folded);
}

#[test]
fn default_fold_should_produce_same_enums() {
    let source = @"enum a { b }";
    let ast = parse::from_str(source);
    let doc = extract::extract(ast, ~"");
    let fld = DefaultFold;
    let folded = fld.fold_doc(doc.clone());
    assert_eq!(doc, folded);
}

#[test]
fn default_parallel_fold_should_produce_same_doc() {
    let source = @"mod a { fn b() { } mod c { fn d() { } } }";
    let ast = parse::from_str(source);
    let doc = extract::extract(ast, ~"");
    let fld = DefaultFold;
    let folded = fld.fold_doc(doc.clone());
    assert_eq!(doc, folded);
}
