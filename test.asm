bits 64
default rel

extern GetStdHandle
extern WriteFile
extern ExitProcess

section .data
    buffer db 0

section .text

print:
    push    rbp         ; Push base pointer to stack
    mov     rbp, rsp    ; Move stack pointer to base pointer
    sub     rsp, 24     ; Leave 3 bytes of nulls

    mov     [buffer], rcx ; Move first argument to buffer

    ; Get STD OUT
    mov     rcx, -11
    call    GetStdHandle
    
    
    mov     rcx, rax    ; Move STD Out to first parameter
    mov     rdx, buffer ; Move buffer to second parameter
    mov     r8, 8       ; Write 8 bytes (max)
    mov     r9, 0       ; Required to be 0
    push    0           ; Required to be 0

    call WriteFile      ; Print

    mov     rsp, rbp    ; Move base pointer to stack pointer
    pop     rbp         ; Get base pointer from stack

    ret

global main
main:
    ; Print "Hello "
    mov     rcx, "Hello "
    call    print

    ; Print "world!"
    mov     rcx, "world!"
    call    print

    ; Print newline
    mov     rcx, 0x0A
    call    print

    ; Exit with 0
    mov     rcx, 0
    call    ExitProcess
