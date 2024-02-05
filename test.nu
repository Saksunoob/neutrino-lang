extern ExitProcess(int) void;

fn main() void {
    let x = 1;
    while x < 10 {
        x = x+1;
    }
    ExitProcess(x);
    ret;
}