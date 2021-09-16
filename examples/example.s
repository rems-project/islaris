test1:
    bl fn1
    mov x28, x0
    str x28, [x27]
    nop

fn1:
    mov w0, 0
    ret

test2:
    cmp x1, 0
    bne 0xc
    mov x0, 1
    b branch2
branch1:
    bl fn2
branch2:
    mov x28, x0
    nop

fn2:
    mov x0, 0
    ret
