extern ExitProcess;

fn main() void {
    let x = 8;
    x = addone(0, 0, 0, 0, 0, x);
    x = addone(0, 0, 0, 0, 0, x);
    ExitProcess(x/2);
}

fn addone(pad1 int, pad2 int, pad3 int, pad4 int, pad5 int, number int) int {
    ret number+1;
}