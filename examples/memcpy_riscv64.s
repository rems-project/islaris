                                        # https://godbolt.org/z/aMTWsK947
                                        # compiled with rv64gc clang 13.0.0 -O2
mcpy:                                   # @mcpy
        beqz    a2, .LBB0_2
.LBB0_1:                                # =>This Inner Loop Header: Depth=1
        lb      a3, 0(a1)
        sb      a3, 0(a0)
        addi    a2, a2, -1
        addi    a0, a0, 1
        addi    a1, a1, 1
        bnez    a2, .LBB0_1
.LBB0_2:
        ret
