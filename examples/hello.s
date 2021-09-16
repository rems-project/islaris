main:
        adrp    x1, .LC0
        mov     x2, 4096
        add	    x1, x1, #0x690
        mov     w0, 72
        movk    x2, 0x101f, lsl 16
.L2:
        strb    w0, [x2]
        ldrb    w0, [x1, 1]!
        cbnz    w0, .L2

.LC0:
        .string "Hello, World!\n"
