// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Operations and constants for `u8`

pub use self::inst::is_ascii;

use num::NumCast;

mod inst {
    pub type T = u8;
    #[allow(non_camel_case_types)]
    pub type T_SIGNED = i8;
    pub static bits: uint = 8;

    // Type-specific functions here. These must be reexported by the
    // parent module so that they appear in core::u8 and not core::u8::u8;

    pub fn is_ascii(x: T) -> bool { return 0 as T == x & 128 as T; }
}

impl NumCast for u8 {
    /**
     * Cast `n` to a `u8`
     */
    #[inline(always)]
    fn from<N:NumCast>(n: N) -> u8 { n.to_u8() }

    #[inline(always)] fn to_u8(&self)    -> u8    { *self          }
    #[inline(always)] fn to_u16(&self)   -> u16   { *self as u16   }
    #[inline(always)] fn to_u32(&self)   -> u32   { *self as u32   }
    #[inline(always)] fn to_u64(&self)   -> u64   { *self as u64   }
    #[inline(always)] fn to_uint(&self)  -> uint  { *self as uint  }

    #[inline(always)] fn to_i8(&self)    -> i8    { *self as i8    }
    #[inline(always)] fn to_i16(&self)   -> i16   { *self as i16   }
    #[inline(always)] fn to_i32(&self)   -> i32   { *self as i32   }
    #[inline(always)] fn to_i64(&self)   -> i64   { *self as i64   }
    #[inline(always)] fn to_int(&self)   -> int   { *self as int   }

    #[inline(always)] fn to_f32(&self)   -> f32   { *self as f32   }
    #[inline(always)] fn to_f64(&self)   -> f64   { *self as f64   }
    #[inline(always)] fn to_float(&self) -> float { *self as float }
}

#[test]
fn test_numcast() {
    fail_unless!((20u     == 20u8.to_uint()));
    fail_unless!((20u8    == 20u8.to_u8()));
    fail_unless!((20u16   == 20u8.to_u16()));
    fail_unless!((20u32   == 20u8.to_u32()));
    fail_unless!((20u64   == 20u8.to_u64()));
    fail_unless!((20i     == 20u8.to_int()));
    fail_unless!((20i8    == 20u8.to_i8()));
    fail_unless!((20i16   == 20u8.to_i16()));
    fail_unless!((20i32   == 20u8.to_i32()));
    fail_unless!((20i64   == 20u8.to_i64()));
    fail_unless!((20f     == 20u8.to_float()));
    fail_unless!((20f32   == 20u8.to_f32()));
    fail_unless!((20f64   == 20u8.to_f64()));

    fail_unless!((20u8 == NumCast::from(20u)));
    fail_unless!((20u8 == NumCast::from(20u8)));
    fail_unless!((20u8 == NumCast::from(20u16)));
    fail_unless!((20u8 == NumCast::from(20u32)));
    fail_unless!((20u8 == NumCast::from(20u64)));
    fail_unless!((20u8 == NumCast::from(20i)));
    fail_unless!((20u8 == NumCast::from(20i8)));
    fail_unless!((20u8 == NumCast::from(20i16)));
    fail_unless!((20u8 == NumCast::from(20i32)));
    fail_unless!((20u8 == NumCast::from(20i64)));
    fail_unless!((20u8 == NumCast::from(20f)));
    fail_unless!((20u8 == NumCast::from(20f32)));
    fail_unless!((20u8 == NumCast::from(20f64)));

    fail_unless!((20u8 == num::cast(20u)));
    fail_unless!((20u8 == num::cast(20u8)));
    fail_unless!((20u8 == num::cast(20u16)));
    fail_unless!((20u8 == num::cast(20u32)));
    fail_unless!((20u8 == num::cast(20u64)));
    fail_unless!((20u8 == num::cast(20i)));
    fail_unless!((20u8 == num::cast(20i8)));
    fail_unless!((20u8 == num::cast(20i16)));
    fail_unless!((20u8 == num::cast(20i32)));
    fail_unless!((20u8 == num::cast(20i64)));
    fail_unless!((20u8 == num::cast(20f)));
    fail_unless!((20u8 == num::cast(20f32)));
    fail_unless!((20u8 == num::cast(20f64)));
}
