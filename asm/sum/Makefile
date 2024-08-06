all:
	riscv64-linux-gnu-gcc -S sum.c
	riscv64-linux-gnu-as -march=rv64i -o sum.o sum.s
	riscv64-linux-gnu-ld -o sum.elf sum.o
