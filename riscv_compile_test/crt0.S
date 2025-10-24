    .section .init
    .globl _start
_start:
    la sp, _stack_top      # set up stack
    call main              # jump to main
    
1:  j 1b                   # infinite loop if main returns
