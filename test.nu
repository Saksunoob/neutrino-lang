extern ExitProcess(int) void;

struct Test {
    a int,
    b int,
}

fn main() int {
    let x = Test{a: 1, b: 2};
    ret 0;
}

fn struct_call_test(num1 Test, num2 bool) int {
    ret num1.a + num1.b;
}