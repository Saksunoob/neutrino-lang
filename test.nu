extern ExitProcess(int) void;

fn main() int {
    let x = 7;
    ret var_size_test(x, true);
}

fn var_size_test(num1 int, num2 bool) int {
    if num2 {
        ret num1;
    }
    ret 0;
}