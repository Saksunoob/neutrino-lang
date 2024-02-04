extern ExitProcess;

fn main() void {
    let x = 8;
    x = addone(x);
    x = addone(x);
    ExitProcess(x/2);
}

fn addone(number int) int {
    ret number+1;
}