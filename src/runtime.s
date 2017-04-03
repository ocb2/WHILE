decimal_length: equ 21  ; maximum length of a base 10 representation of a 64 bit number

section .text
global print_decimal
global newline

print_decimal:
    push rdx
    push rdi
    push rsi

    mov rdi, rsp
    add rsp, decimal_length
.loop:
    mov rdx, 0
    mov rsi, 10
    div rsi

    add rdx, 0x30
    mov [rsp], dl
    dec rsp

    cmp rax, 0
    jne .loop

    mov rax, 0x01
    mov rsi, rsp

    sub rsp, rdi
    mov rdx, (decimal_length + 1)
    sub rdx, rsp

    mov rsp, rdi
    mov rdi, 0x01
    syscall

    pop rsi
    pop rdi
    pop rdx
    ret

newline:
    push rdi
    push rsi
    push rdx

    mov rax, 0x01
    mov rdi, 0x01
    mov rsi, ._
    mov rdx, 0x01
    syscall

    pop rdx
    pop rsi
    pop rdi
    ret
._: db 0xA