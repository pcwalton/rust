// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! LLVM Type-Based Alias Analysis (TBAA) information.

use extra::bitv::Bitv;
use std::cast;
use std::libc::c_uint;

use lib::llvm::{ContextRef, ValueRef};
use lib::llvm::llvm::{LLVMMDNodeInContext, LLVMMDStringInContext};
use middle::trans::common;

static ROOT_NODE_STRING: &'static str = "Rust root node";

static TYPE_NODE_STRING: &'static str = "Rust type node";

pub struct TbaaInfo {
    root_node: Option<ValueRef>,
    nodes: ~[ValueRef],
}

impl TbaaInfo {
    pub fn new() -> TbaaInfo {
        TbaaInfo {
            root_node: None,
            nodes: ~[],
        }
    }

    /// Initializes the root node.
    pub fn init(&mut self, llcx: ContextRef) {
        unsafe {
            let vals = [
                LLVMMDStringInContext(llcx,
                                      cast::transmute(&ROOT_NODE_STRING[0]),
                                      ROOT_NODE_STRING.len() as c_uint)
            ];
            self.root_node = Some(LLVMMDNodeInContext(llcx, &vals[0], 1))
        }
    }

    /// Returns the aliasing TBAA nodes.
    pub fn create_node(&mut self, llcx: ContextRef) -> ValueRef {
        let chain = match self.nodes.last() {
            None => self.root_node.unwrap(),
            Some(node) => *node,
        };
        let node = unsafe {
            let vals = [
                LLVMMDStringInContext(llcx,
                                      cast::transmute(&TYPE_NODE_STRING[0]),
                                      TYPE_NODE_STRING.len() as c_uint),
                chain,
            ];
            LLVMMDNodeInContext(llcx, &vals[0], 2)
        };
        self.nodes.push(node);
        node
    }

    /// Creates a new TBAA-struct node from the given bitvector and returns
    /// it. See the comments in `adt::compute_padding` for more details as to
    /// the structure of this bitfield.
    pub fn create_struct_node(&mut self, llcx: ContextRef, bitvector: &Bitv)
                              -> ValueRef {
        let mut vals = ~[];

        let add_range = |start: u64, len: u64| {
            vals.push(common::C_i64(start as i64));
            vals.push(common::C_i64(len as i64));
            vals.push(self.create_node(llcx));
        };

        let mut start: u64 = 0;
        for end in range(1, bitvector.len() as u64) {
            if bitvector.get(end as uint) {
                continue
            }
            if start != end {
                add_range(start, end - start)
            }
            start = end + 1;
        }
        if start != bitvector.len() as u64 - 1 {
            add_range(start, bitvector.len() as u64 - 1 - start)
        }

        unsafe {
            LLVMMDNodeInContext(llcx, &vals[0], 3)
        }
    }
}

