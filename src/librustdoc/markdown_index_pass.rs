// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Build indexes as appropriate for the markdown pass

use astsrv;
use config;
use doc::ItemUtils;
use doc;
use fold::Fold;
use fold;
use markdown_pass;
use markdown_writer;
use pass::Pass;

pub fn mk_pass(config: config::Config) -> @Pass {
    @MarkdownIndexPass {
        config: config,
    } as @Pass
}

pub struct MarkdownIndexPass {
    config: config::Config,
}

impl Pass for MarkdownIndexPass {
    fn name(&self) -> ~str {
        ~"markdown_index"
    }

    fn run(&self, _: astsrv::Srv, doc: doc::Doc) -> doc::Doc {
        self.fold_doc(doc)
    }
}

impl Fold for MarkdownIndexPass {
    fn fold_mod(&self, doc: doc::ModDoc) -> doc::ModDoc {
        let doc = fold::default_fold_mod(self, doc);

        doc::ModDoc {
            index: Some(build_mod_index(doc.clone(), self.config.clone())),
            .. doc
        }
    }

    fn fold_nmod(&self, doc: doc::NmodDoc) -> doc::NmodDoc {
        let doc = fold::default_fold_nmod(self, doc);

        doc::NmodDoc {
            index: Some(build_nmod_index(doc.clone(), self.config.clone())),
            .. doc
        }
    }
}

fn build_mod_index(
    doc: doc::ModDoc,
    config: config::Config
) -> doc::Index {
    doc::Index {
        entries: doc.items.map(|doc| {
            item_to_entry((*doc).clone(), &config)
        })
    }
}

fn build_nmod_index(
    doc: doc::NmodDoc,
    config: config::Config
) -> doc::Index {
    doc::Index {
        entries: doc.fns.map(|doc| {
            item_to_entry(doc::FnTag((*doc).clone()), &config)
        })
    }
}

fn item_to_entry(
    doc: doc::ItemTag,
    config: &config::Config
) -> doc::IndexEntry {
    let link = match doc {
      doc::ModTag(_) | doc::NmodTag(_)
      if config.output_style == config::DocPerMod => {
        markdown_writer::make_filename(config,
                                       doc::ItemPage(doc.clone())).to_str()
      }
      _ => {
        ~"#" + pandoc_header_id(markdown_pass::header_text(doc.clone()))
      }
    };

    doc::IndexEntry {
        kind: markdown_pass::header_kind(doc.clone()),
        name: markdown_pass::header_name(doc.clone()),
        brief: doc.brief(),
        link: link
    }
}

pub fn pandoc_header_id(header: &str) -> ~str {

    // http://johnmacfarlane.net/pandoc/README.html#headers

    let header = remove_formatting(header);
    let header = remove_punctuation(header);
    let header = replace_with_hyphens(header);
    let header = convert_to_lowercase(header);
    let header = remove_up_to_first_letter(header);
    let header = maybe_use_section_id(header);
    return header;

    fn remove_formatting(s: &str) -> ~str {
        s.replace("`", "")
    }
    fn remove_punctuation(s: &str) -> ~str {
        let s = s.replace("<", "");
        let s = s.replace(">", "");
        let s = s.replace("[", "");
        let s = s.replace("]", "");
        let s = s.replace("(", "");
        let s = s.replace(")", "");
        let s = s.replace("@~", "");
        let s = s.replace("~", "");
        let s = s.replace("/", "");
        let s = s.replace(":", "");
        let s = s.replace("&", "");
        let s = s.replace("^", "");
        let s = s.replace(",", "");
        let s = s.replace("'", "");
        let s = s.replace("+", "");
        return s;
    }
    fn replace_with_hyphens(s: &str) -> ~str {
        // Collapse sequences of whitespace to a single dash
        // XXX: Hacky implementation here that only covers
        // one or two spaces.
        let s = s.trim();
        let s = s.replace("  ", "-");
        let s = s.replace(" ", "-");
        return s;
    }
    // FIXME: #4318 Instead of to_ascii and to_str_ascii, could use
    // to_ascii_consume and to_str_consume to not do a unnecessary copy.
    fn convert_to_lowercase(s: &str) -> ~str { s.to_ascii().to_lower().to_str_ascii() }
    fn remove_up_to_first_letter(s: &str) -> ~str { s.to_str() }
    fn maybe_use_section_id(s: &str) -> ~str { s.to_str() }
}

#[cfg(test)]
mod test {

    use astsrv;
    use attr_pass;
    use config;
    use desc_to_brief_pass;
    use doc;
    use extract;
    use markdown_index_pass::MarkdownIndexPass;
    use pass::Pass;
    use path_pass;
    use prune_hidden_pass;
    use super::pandoc_header_id;

    fn mk_doc(output_style: config::OutputStyle, source: ~str)
               -> doc::Doc {
        do astsrv::from_str(source) |srv| {
            let config = config::Config {
                output_style: output_style,
                .. config::default_config(&Path("whatever"))
            };
            let doc = extract::from_srv(srv.clone(), ~"");
            let doc = attr_pass::mk_pass().run(srv.clone(), doc);
            let doc = prune_hidden_pass::mk_pass().run(srv.clone(), doc);
            let doc = desc_to_brief_pass::mk_pass().run(srv.clone(), doc);
            let doc = path_pass::mk_pass().run(srv.clone(), doc);

            MarkdownIndexPass {
                config: config,
            }.run(srv.clone(), doc)
        }
    }

    #[test]
    fn should_remove_punctuation_from_headers() {
        assert!(pandoc_header_id("impl foo of bar<A>") ==
                ~"impl-foo-of-bara");
        assert!(pandoc_header_id("impl of num::num for int")
                == ~"impl-of-numnum-for-int");
        assert!(pandoc_header_id("impl of num::num for int/&")
                == ~"impl-of-numnum-for-int");
        assert!(pandoc_header_id("impl of num::num for ^int")
                == ~"impl-of-numnum-for-int");
        assert!(pandoc_header_id("impl for & condvar")
                == ~"impl-for-condvar");
        assert!(pandoc_header_id("impl of Select<T, U> for (Left, Right)")
                == ~"impl-of-selectt-u-for-left-right");
        assert!(pandoc_header_id("impl of Condition<'self, T, U>")
                == ~"impl-of-conditionself-t-u");
        assert!(pandoc_header_id("impl of Condition<T: Clone>")
                == ~"impl-of-conditiont-clone");
    }

    #[test]
    fn should_trim_whitespace_after_removing_punctuation() {
        assert_eq!(pandoc_header_id("impl foo for ()"), ~"impl-foo-for");
    }

    #[test]
    fn should_index_mod_contents() {
        let doc = mk_doc(
            config::DocPerCrate,
            ~"mod a { } fn b() { }"
        );
        assert!(doc.cratemod().index.unwrap().entries[0] == doc::IndexEntry {
            kind: ~"Module",
            name: ~"a",
            brief: None,
            link: ~"#module-a"
        });
        assert!(doc.cratemod().index.unwrap().entries[1] == doc::IndexEntry {
            kind: ~"Function",
            name: ~"b",
            brief: None,
            link: ~"#function-b"
        });
    }

    #[test]
    fn should_index_mod_contents_multi_page() {
        let doc = mk_doc(
            config::DocPerMod,
            ~"mod a { } fn b() { }"
        );
        assert_eq!(doc.cratemod().index.unwrap().entries[0], doc::IndexEntry {
            kind: ~"Module",
            name: ~"a",
            brief: None,
            link: ~"a.html"
        });
        assert_eq!(doc.cratemod().index.unwrap().entries[1], doc::IndexEntry {
            kind: ~"Function",
            name: ~"b",
            brief: None,
            link: ~"#function-b"
        });
    }

    #[test]
    fn should_add_brief_desc_to_index() {
        let doc = mk_doc(
            config::DocPerMod,
            ~"#[doc = \"test\"] mod a { }"
        );
        assert_eq!(doc.cratemod().index.unwrap().entries[0].brief, Some(~"test"));
    }

    #[test]
    fn should_index_foreign_mod_contents() {
        let doc = mk_doc(
            config::DocPerCrate,
            ~"extern { fn b(); }"
        );
        // hidden __std_macros module at the start.
        assert_eq!(doc.cratemod().nmods()[0].index.unwrap().entries[0],
                   doc::IndexEntry {
                       kind: ~"Function",
                       name: ~"b",
                       brief: None,
                       link: ~"#function-b"
                   });
    }
}
