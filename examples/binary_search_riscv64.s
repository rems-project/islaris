                                        # https://godbolt.org/z/9fP8fr1e3
binary_search:                          # @binary_search
        addi    sp, sp, -64
        sd      ra, 56(sp)                      # 8-byte Folded Spill
        sd      s0, 48(sp)                      # 8-byte Folded Spill
        sd      s1, 40(sp)                      # 8-byte Folded Spill
        sd      s2, 32(sp)                      # 8-byte Folded Spill
        sd      s3, 24(sp)                      # 8-byte Folded Spill
        sd      s4, 16(sp)                      # 8-byte Folded Spill
        sd      s5, 8(sp)                       # 8-byte Folded Spill
        beqz    a2, .LBB0_5
        mv      s2, a3
        mv      s5, a2
        mv      s3, a1
        mv      s4, a0
        mv      s1, zero
        j       .LBB0_3
.LBB0_2:                                #   in Loop: Header=BB0_3 Depth=1
        mv      s5, s0
        bgeu    s1, s5, .LBB0_6
.LBB0_3:                                # =>This Inner Loop Header: Depth=1
        sub     a0, s5, s1
        srli    a0, a0, 1
        add     s0, a0, s1
        slli    a0, s0, 3
        add     a0, a0, s3
        ld      a0, 0(a0)
        mv      a1, s2
        jalr    s4
        beqz    a0, .LBB0_2
        addi    s1, s0, 1
        bltu    s1, s5, .LBB0_3
        j       .LBB0_6
.LBB0_5:
        mv      s1, zero
.LBB0_6:
        mv      a0, s1
        ld      s5, 8(sp)                       # 8-byte Folded Reload
        ld      s4, 16(sp)                      # 8-byte Folded Reload
        ld      s3, 24(sp)                      # 8-byte Folded Reload
        ld      s2, 32(sp)                      # 8-byte Folded Reload
        ld      s1, 40(sp)                      # 8-byte Folded Reload
        ld      s0, 48(sp)                      # 8-byte Folded Reload
        ld      ra, 56(sp)                      # 8-byte Folded Reload
        addi    sp, sp, 64
        ret
compare_int:                            # @compare_int
        sltu    a0, a1, a0
        xori    a0, a0, 1
        ret
