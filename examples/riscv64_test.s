test:
    mv      a0, zero
    addi    a0, a0, 1
    sd      a1, 8(sp)
    ld      a1, 8(sp)
    beq     a0, a1, .END
    nop
.END:
    nop
