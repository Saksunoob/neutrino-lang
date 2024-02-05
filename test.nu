extern ExitProcess(int) void;

fn main() void {
    let x = cond_test();
    ExitProcess(x);
}

fn cond_test() int {
    let x = 0;
    if x == 1 {
        ret 1;
    }
    ret 0;
}