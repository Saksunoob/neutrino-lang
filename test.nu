struct Test {
    a int,
    b int
}

struct WithRef {
    x &Test
}

fn main() int {
    let x = Test {a: 1, b: 2};
    let y = WithRef {x: &x};
    ret y.x.b;
}