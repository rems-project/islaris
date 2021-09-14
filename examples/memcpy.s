mcpy:
        cbz     x2, .L1
        mov     x3, 0
.L3:
        ldrb    w4, [x1, x3]
        strb    w4, [x0, x3]
        add     x3, x3, 1
        cmp     x2, x3
        bne     .L3
.L1:
        ret
