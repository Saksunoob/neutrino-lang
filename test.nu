extern ExitProcess(int) void;

struct Test {
    a int,
    b int,
}

struct Test2 {
    a Test,
    b int,
}

fn main() int {
    let x = Test2{a: Test{a: 1, b: 2}, b: 3};
    x.a.b = 4;
    ret x.a.b;
}