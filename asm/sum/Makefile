all:
	riscv64-linux-gnu-gcc -march=rv64i -mabi=lp64 -S sum.c
	riscv64-linux-gnu-as -march=rv64i -o sum.o sum.s
	riscv64-linux-gnu-ld -o sum.elf sum.o
