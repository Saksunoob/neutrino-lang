extern ExitProcess;

fn main() void {
    let x = 1;
    x = addall(x, 2, 4, 8, 16, 32);
    ExitProcess(x);
}

fn addall(num1 int, num2 int, num3 int, num4 int, num5 int, num6 int) int {
    ret num1+num2+num3+num4+num5+num6;
}