.globl main

.text
main:
	# Load initial values
    addi x1, x0, 1      # x1 will hold the wdata
    addi x31, x0, 0     # x31 will hold the waddr
    addi x30, x0, 1024  # 1024 is the mem size

    loop:
    sw x1, 0(x31)
    addi x31, x31, 4
    addi x1, x1, 1
    bne x31, x30, loop
