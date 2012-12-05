struct S {
    x: int,
    drop {
        io::println("goodbye");
    }
}

fn main() {
    let x = Some(S { x: 3 });
    match x {
        Some(y) => io::println(y.x.to_str()),
        None => {}
    }
}

