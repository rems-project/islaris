test:
    mv      a0, zero
    addi    a0, a0, 1
    beq     a0, a1, .END
    nop
.END:
    nop
