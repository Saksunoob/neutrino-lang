bits 64
default rel
extern ExitProcess
section .text
global main
main:
	MOV RAX, 8
	PUSH RAX
	MOV RAX, [RSP+0]
	PUSH RAX
	POP RCX
	SUB RSP, 32
	CALL addone
	PUSH RAX
	MOV RAX, [RSP+0]
	PUSH RAX
	POP RCX
	SUB RSP, 32
	CALL addone
	PUSH RAX
	MOV RAX, 2
	PUSH RAX
	MOV RAX, [RSP+8]
	POP RBX
	MOV RDX, 0
	IDIV RBX
	PUSH RAX
	POP RCX
	SUB RSP, 32
	CALL ExitProcess
	ADD RSP, 8
global addone
addone:
	PUSH RCX
	MOV RAX, 1
	PUSH RAX
	MOV RAX, [RSP+8]
	POP RBX
	ADD RAX, RBX
	ADD RSP, 8
	POP RBX
	ADD RSP, 32
	PUSH RBX
	RET
	ADD RSP, 8
