memory_instructions:
    stp	x0, x1, [sp, #-16]!
    ldr	x0, [x1]
    str	x9, [x1]
