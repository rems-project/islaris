binary_search:                          // @binary_search
        stp     x29, x30, [sp, #-64]!           // 16-byte Folded Spill
        stp     x24, x23, [sp, #16]             // 16-byte Folded Spill
        stp     x22, x21, [sp, #32]             // 16-byte Folded Spill
        stp     x20, x19, [sp, #48]             // 16-byte Folded Spill
        mov     x29, sp
        cbz     x2, .LBB0_3
        mov     x19, x3
        mov     x20, x2
        mov     x21, x1
        mov     x22, x0
        mov     x23, xzr
.LBB0_2:                                // =>This Inner Loop Header: Depth=1
        sub     x8, x20, x23
        add     x24, x23, x8, lsr #1
        ldr     x0, [x21, x24, lsl #3]
        mov     x1, x19
        blr     x22
        tst     w0, #0x1
        csel    x20, x20, x24, ne
        csinc   x23, x23, x24, eq
        cmp     x20, x23
        b.hi    .LBB0_2
        b       .LBB0_4
.LBB0_3:
        mov     x23, xzr
.LBB0_4:
        mov     x0, x23
        ldp     x20, x19, [sp, #48]             // 16-byte Folded Reload
        ldp     x22, x21, [sp, #32]             // 16-byte Folded Reload
        ldp     x24, x23, [sp, #16]             // 16-byte Folded Reload
        ldp     x29, x30, [sp], #64             // 16-byte Folded Reload
        ret
compare_int:                            // @compare_int
        cmp     x0, x1
        cset    w0, ls
        ret
