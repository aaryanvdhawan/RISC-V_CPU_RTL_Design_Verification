CC       = riscv64-unknown-elf-gcc
OBJDUMP  = riscv64-unknown-elf-objdump

ARCH_FLAGS = -march=rv32im -mabi=ilp32
CFLAGS     = $(ARCH_FLAGS) -O2 -c
LDFLAGS    = -T link.ld $(ARCH_FLAGS) -nostdlib -nostartfiles -nodefaultlibs

C_SRC   = tst.c
ASM_SRC = crt0.S
OBJ     = $(C_SRC:.c=.o) $(ASM_SRC:.S=.o)
ELF     = tst.elf
DISASM  = disasm.txt
HEX     =/home/briccs_fpga/riscv_compile_test



.PHONY: all clean

# The default 'all' target will now create both the disassembly and the hex files.
all: $(DISASM) $(HEX)

# Link the final ELF executable from all object files
$(ELF): $(OBJ)
	$(CC) $(LDFLAGS) -o $@ $^

# Disassemble the ELF file to create the full assembly listing
$(DISASM): $(ELF)
	$(OBJDUMP) -d -S $< > $@

# Extract only the hexadecimal machine code from the disassembly
$(HEX): $(DISASM)
	awk '{print $$2}' $< | grep -E '^[0-9a-f]+$$' > $@

# Generic rule to build a .o file from a .c file
%.o: %.c
	$(CC) $(CFLAGS) -o $@ $<

# Generic rule to build a .o file from a .S file
%.o: %.S
	$(CC) $(ARCH_FLAGS) -c -o $@ $<

# Removes all generated files
clean:
	rm -f $(OBJ) $(ELF) $(DISASM) $(HEX)

