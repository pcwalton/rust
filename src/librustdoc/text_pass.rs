// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generic pass for performing an operation on all descriptions


use astsrv;
use doc::ItemUtils;
use doc;
use fold::Fold;
use fold;
use pass::Pass;

pub fn mk_pass(name: ~str, op: @Op) -> @Pass {
    @WrappedOp {
        name: name,
        op: op,
    } as @Pass
}

pub trait Op {
    fn op(&self, s: &str) -> ~str;
}

struct WrappedOp {
    name: ~str,
    op: @Op,
}

impl Clone for WrappedOp {
    fn clone(&self) -> WrappedOp {
        WrappedOp {
            name: self.name.clone(),
            op: self.op,
        }
    }
}

impl Pass for WrappedOp {
    fn name(&self) -> ~str {
        self.name.clone()
    }

    fn run(&self, _: astsrv::Srv, doc: doc::Doc) -> doc::Doc {
        self.fold_doc(doc)
    }
}

impl Fold for WrappedOp {
    fn fold_enum(&self, doc: doc::EnumDoc) -> doc::EnumDoc {
        let doc = fold::default_fold_enum(self, doc);

        doc::EnumDoc {
            variants: do doc.variants.map |variant| {
                doc::VariantDoc {
                    desc: maybe_apply_op(self, &variant.desc),
                    .. (*variant).clone()
                }
            },
            .. doc
        }
    }

    fn fold_item(&self, doc: doc::ItemDoc) -> doc::ItemDoc {
        doc::ItemDoc {
            brief: maybe_apply_op(self, &doc.brief),
            desc: maybe_apply_op(self, &doc.desc),
            sections: apply_to_sections(self, doc.sections.clone()),
            .. doc
        }
    }

    fn fold_trait(&self, doc: doc::TraitDoc) -> doc::TraitDoc {
        let doc = fold::default_fold_trait(self, doc);

        doc::TraitDoc {
            methods: apply_to_methods(self, doc.methods.clone()),
            .. doc
        }
    }

    fn fold_impl(&self, doc: doc::ImplDoc) -> doc::ImplDoc {
        let doc = fold::default_fold_impl(self, doc);

        doc::ImplDoc {
            methods: apply_to_methods(self, doc.methods.clone()),
            .. doc
        }
    }
}

fn maybe_apply_op(op: &WrappedOp, s: &Option<~str>) -> Option<~str> {
    s.map(|s| op.op.op(*s) )
}

fn apply_to_sections(op: &WrappedOp, sections: ~[doc::Section])
                     -> ~[doc::Section] {
    sections.map(|section| doc::Section {
        header: op.op.op(section.header.clone()),
        body: op.op.op(section.body.clone())
    })
}

fn apply_to_methods(op: &WrappedOp, docs: ~[doc::MethodDoc])
                    -> ~[doc::MethodDoc] {
    do docs.map |doc| {
        doc::MethodDoc {
            brief: maybe_apply_op(op, &doc.brief),
            desc: maybe_apply_op(op, &doc.desc),
            sections: apply_to_sections(op, doc.sections.clone()),
            .. (*doc).clone()
        }
    }
}

#[cfg(test)]
mod test {

    use astsrv;
    use attr_pass;
    use desc_to_brief_pass;
    use doc;
    use extract;
    use sectionalize_pass;
    use text_pass::{Op, mk_pass};

    struct TestOp;

    impl Op for TestOp {
        fn op(&self, s: &str) -> ~str {
            s.trim().to_owned()
        }
    }

    fn mk_doc(source: ~str) -> doc::Doc {
        do astsrv::from_str(source.clone()) |srv| {
            let doc = extract::from_srv(srv.clone(), ~"");
            let doc = attr_pass::mk_pass().run(srv.clone(), doc);
            let doc = desc_to_brief_pass::mk_pass().run(srv.clone(), doc);
            let doc = sectionalize_pass::mk_pass().run(srv.clone(), doc);
            mk_pass(~"", @TestOp as @Op).run(srv.clone(), doc)
        }
    }

    #[test]
    fn should_execute_op_on_enum_brief() {
        let doc = mk_doc(~"#[doc = \" a \"] enum a { b }");
        assert_eq!(doc.cratemod().enums()[0].brief(), Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_enum_desc() {
        let doc = mk_doc(~"#[doc = \" a \"] enum a { b }");
        assert_eq!(doc.cratemod().enums()[0].desc(), Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_variant_desc() {
        let doc = mk_doc(~"enum a { #[doc = \" a \"] b }");
        assert!(doc.cratemod().enums()[0].variants[0].desc == Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_trait_brief() {
        let doc = mk_doc(
            ~"#[doc = \" a \"] trait i { fn a(); }");
        assert_eq!(doc.cratemod().traits()[0].brief(), Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_trait_desc() {
        let doc = mk_doc(
            ~"#[doc = \" a \"] trait i { fn a(); }");
        assert_eq!(doc.cratemod().traits()[0].desc(), Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_trait_method_brief() {
        let doc = mk_doc(
            ~"trait i { #[doc = \" a \"] fn a(); }");
        assert!(doc.cratemod().traits()[0].methods[0].brief == Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_trait_method_desc() {
        let doc = mk_doc(
            ~"trait i { #[doc = \" a \"] fn a(); }");
        assert!(doc.cratemod().traits()[0].methods[0].desc == Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_impl_brief() {
        let doc = mk_doc(
            ~"#[doc = \" a \"] impl int { fn a() { } }");
        assert_eq!(doc.cratemod().impls()[0].brief(), Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_impl_desc() {
        let doc = mk_doc(
            ~"#[doc = \" a \"] impl int { fn a() { } }");
        assert_eq!(doc.cratemod().impls()[0].desc(), Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_impl_method_brief() {
        let doc = mk_doc(
            ~"impl int { #[doc = \" a \"] fn a() { } }");
        assert!(doc.cratemod().impls()[0].methods[0].brief == Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_impl_method_desc() {
        let doc = mk_doc(
            ~"impl int { #[doc = \" a \"] fn a() { } }");
        assert!(doc.cratemod().impls()[0].methods[0].desc == Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_type_brief() {
        let doc = mk_doc(
            ~"#[doc = \" a \"] type t = int;");
        assert_eq!(doc.cratemod().types()[0].brief(), Some(~"a"));
    }

    #[test]
    fn should_execute_op_on_type_desc() {
        let doc = mk_doc(
            ~"#[doc = \" a \"] type t = int;");
        assert_eq!(doc.cratemod().types()[0].desc(), Some(~"a"));
    }

    #[test]
    fn should_execute_on_item_section_headers() {
        let doc = mk_doc(
            ~"#[doc = \"\
              #    Header    \n\
              Body\"]\
              fn a() { }");
        assert!(doc.cratemod().fns()[0].sections()[0].header == ~"Header");
    }

    #[test]
    fn should_execute_on_item_section_bodies() {
        let doc = mk_doc(
            ~"#[doc = \"\
              # Header\n\
              Body      \"]\
              fn a() { }");
        assert!(doc.cratemod().fns()[0].sections()[0].body == ~"Body");
    }

    #[test]
    fn should_execute_on_trait_method_section_headers() {
        let doc = mk_doc(
            ~"trait i {
#[doc = \"\
              # Header    \n\
              Body\"]\
              fn a(); }");
        assert!(doc.cratemod().traits()[0].methods[0].sections[0].header
                == ~"Header");
    }

    #[test]
    fn should_execute_on_trait_method_section_bodies() {
        let doc = mk_doc(
            ~"trait i {
#[doc = \"\
              # Header\n\
              Body     \"]\
              fn a(); }");
        assert!(doc.cratemod().traits()[0].methods[0].sections[0].body ==
                ~"Body");
    }

    #[test]
    fn should_execute_on_impl_method_section_headers() {
        let doc = mk_doc(
            ~"impl bool {
#[doc = \"\
              # Header   \n\
              Body\"]\
              fn a() { } }");
        assert!(doc.cratemod().impls()[0].methods[0].sections[0].header
                == ~"Header");
    }

    #[test]
    fn should_execute_on_impl_method_section_bodies() {
        let doc = mk_doc(
            ~"impl bool {
#[doc = \"\
              # Header\n\
              Body    \"]\
              fn a() { } }");
        assert!(doc.cratemod().impls()[0].methods[0].sections[0].body ==
                ~"Body");
    }
}
