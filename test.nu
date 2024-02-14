struct Test {
    a int,
    b int
}

fn main() int {
    let x = Test {a: 1, b: 2};
    let y = &x;
    ret x.a;
}