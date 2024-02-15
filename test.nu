struct Test {
    a int,
    b int
}

fn main() int {
    let x = Test {a: 1, b: 2};
    let y = &x;
    y.a = x.b;
    x.b = y.a + 1;
    ret x.a + y.b;
}