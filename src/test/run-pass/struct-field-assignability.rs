struct Foo {
    x: &int
}

pub fn main() {
    let f = Foo { x: @3 };
    fail_unless!(*f.x == 3);
}

