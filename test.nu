extern ExitProcess;

fn main() void {
    let x = 1;
    if x {
        let y = 5;
        x = x+y;
    }
    ExitProcess(x);
}

fn test() void {
}