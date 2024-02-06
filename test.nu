extern ExitProcess(int) void;

fn main() int {
    let x = 1;
    while x < 10 {
        x = x + 1;
    }
    ret x;
}

fn cond_test() int {
    let x = 1;
    if x == 1 {
        ret 1;
    }
    ret 0;
}