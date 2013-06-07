struct Foo {
    f: @mut int,
}

impl Drop for Foo { //~ ERROR cannot implement a destructor on a structure that does not satisfy Send
    fn finalize(&self) {
        *self.f = 10;
    }
}

fn main() { }
