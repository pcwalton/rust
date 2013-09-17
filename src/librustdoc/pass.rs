// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.



use astsrv;
use doc;
use time;

#[cfg(test)] use extract;

/// A single operation on the document model
pub trait Pass {
    fn name(&self) -> ~str;
    fn run(&self, srv: astsrv::Srv, doc: doc::Doc) -> doc::Doc;
}

pub fn run_passes(
    srv: astsrv::Srv,
    doc: doc::Doc,
    passes: ~[@Pass]
) -> doc::Doc {
    let mut passno = 0;
    do passes.iter().fold(doc) |doc, pass| {
        debug!("pass #%d", passno);
        passno += 1;
        do time(pass.name()) {
            pass.run(srv.clone(), doc.clone())
        }
    }
}

