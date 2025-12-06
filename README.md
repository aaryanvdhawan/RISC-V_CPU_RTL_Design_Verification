# RISC-V Formal Verification Module and Testbench

This document contains a SystemVerilog verification module for a RISCV single-cycle CPU along with its testbench. The verification module checks registers, memory, and instruction execution correctness.


<img width="1059" height="1050" alt="image" src="https://github.com/user-attachments/assets/df74740a-f426-4fcb-8040-2ccab54e8dbb" />



![netlist_CPU](https://github.com/user-attachments/assets/18b16eb1-f4b9-4fa5-a699-4b90dc9fae68)


---



## 1. Instruction Table

# Generate low level instructions from C code using risc64-gcc-elf toolchain

<img width="827" height="424" alt="image" src="https://github.com/user-attachments/assets/9e6d882a-3a16-40b4-a3f1-e4bb0e087fe3" />


## risc64-gcc-elf toolchain Disassembly Commands

```bash
# Install RISC-V toolchain
sudo apt update
sudo apt install gcc-riscv64-unknown-elf

# Verify toolchain installation
riscv64-unknown-elf-gcc --version

# Download the folder riscv_compile_test and navigate to project directory
cd /path/to/your/riscv_compile_test

# Edit tst.c to include the C code you want to disassemble
nano tst.c  # Replace with your preferred editor (e.g., vim, code)

# Clean previous build artifacts
make clean

# Compile and generate disassembly
make

# View disassembly with hex codes and instructions
cat disasm.txt
```

# Target C Code Snippet

```c
#include <stdio.h>

int main() {
    // Initialize registers (using variables to represent RISC-V registers)
    int x[32] = {0};  // All registers x0-x31, x0 is hardwired to 0
    int memory[256] = {0};  // Simple memory initialization for emulating datamemory address
    
    // Instruction execution
    // 0x000: nop - No operation
    // No C equivalent needed
    
    // 0x004: addi x2, x0, 5 - x2 = 5
    x[2] = x[0] + 5;  // x2 = 0 + 5 = 5
    
    // 0x008: addi x3, x0, 12 - x3 = 12
    x[3] = x[0] + 12;  // x3 = 0 + 12 = 12
    
    // 0x00C: addi x7, x3, -9 - x7 = 12 - 9 = 3
    x[7] = x[3] + (-9);  // x7 = 12 - 9 = 3
    
    // 0x010: or x4, x7, x2 - x4 = 3 OR 5 = 7
    x[4] = x[7] | x[2];  // x4 = 3 | 5 = 7
    
    // 0x014: and x5, x3, x4 - x5 = 12 AND 7 = 4
    x[5] = x[3] & x[4];  // x5 = 12 & 7 = 4
    
    // 0x018: add x5, x5, x4 - x5 = 4 + 7 = 11
    x[5] = x[5] + x[4];  // x5 = 4 + 7 = 11
    
    // 0x01C: beq x5, x7, end - if (11==3)? no branch
    if (x[5] == x[7]) {
        goto end;
    }
    
    // 0x020: slt x4, x3, x4 - x4 = (12 < 7) = 0
    x[4] = (x[3] < x[4]) ? 1 : 0;  // x4 = (12 < 7) ? 1 : 0 = 0
    
    // 0x024: beq x4, x0, around - if (0==0)? branch taken
    if (x[4] == x[0]) {
        goto around;
    }
    
    // 0x028: addi x5, x0, 0 - skipped (branch taken)
    x[5] = x[0] + 0;  // This line would be skipped in actual execution
    
around:
    // 0x02C: slt x4, x7, x2 - x4 = (3 < 5) = 1
    x[4] = (x[7] < x[2]) ? 1 : 0;  // x4 = (3 < 5) ? 1 : 0 = 1
    
    // 0x030: add x7, x4, x5 - x7 = 1 + 11 = 12
    x[7] = x[4] + x[5];  // x7 = 1 + 11 = 12
    
    // 0x034: sub x7, x7, x2 - x7 = 12 - 5 = 7
    x[7] = x[7] - x[2];  // x7 = 12 - 5 = 7
    
    // 0x038: sw x7, 84(x3) - Mem[x3+84] = 7, Mem[12+84=96] = 7
    memory[96/4] = x[7];  // Assuming word-addressable memory
    
    // 0x03C: lw x2, 96(x0) - x2 = Mem[96] = 7
    x[2] = memory[96/4];  // x2 = 7
    
    // 0x040: add x9, x2, x5 - x9 = 7 + 11 = 18
    x[9] = x[2] + x[5];  // x9 = 7 + 11 = 18
    
    // 0x044: jal x0, 8 - Jump to PC+8 = 0x04C
    goto jump_target;
    
    // 0x048: addi x2, x0, 1 - skipped (due to jump)
    x[2] = x[0] + 1;  // This line is skipped
    
jump_target:
    // 0x04C: add x2, x2, x9 - x2 = 7 + 18 = 25
    x[2] = x[2] + x[9];  // x2 = 7 + 18 = 25
    
    // 0x050: sw x2, 32(x3) - Mem[x3+32] = 25, Mem[12+32=44] = 25
    memory[44/4] = x[2];
    
    // Loop simulation (instructions 0x054-0x064)
    // 0x054: addi x10, x0, 5 - x10 = 5
    x[10] = x[0] + 5;
    
    // 0x058: addi x11, x0, 0 - x11 = 0
    x[11] = x[0] + 0;
    
    // This simulates the loop from 0x05C to 0x064
    for (; x[10] > 0; x[10]--) {
        // 0x05C: addi x11, x11, 1 - x11 = x11 + 1
        x[11] = x[11] + 1;
        // 0x060: addi x10, x10, -1 - x10 = x10 - 1
        // Handled in for loop decrement
        // 0x064: beq x10, x0, -16 - branch back if x10 == 0
        // Handled by for loop condition
    }
    
    // 0x068: sw x11, 100(x0) - Mem[100] = 1 (final value after loop)
    memory[100/4] = x[11];
    
    // 0x06C: lw x12, 100(x0) - x12 = Mem[100] = 1
    x[12] = memory[100/4];
    
    // 0x070: slli x13, x12, 2 - x13 = 1 << 2 = 4
    x[13] = x[12] << 2;
    
    // 0x074: srli x14, x13, 1 - x14 = 4 >> 1 = 2 (logical shift)
    x[14] = (unsigned int)x[13] >> 1;
    
    // 0x078: srai x15, x14, 2 - x15 = 2 >> 2 = 0 (arithmetic shift)
    x[15] = x[14] >> 2;
    
    // 0x07C: xor x16, x13, x13 - x16 = 4 XOR 4 = 0
    x[16] = x[13] ^ x[13];
    
    // 0x080: add x17, x16, x16 - x17 = 0 + 0 = 0
    x[17] = x[16] + x[16];

end:
    // Print final register values to verify
    printf("Final register values:\n");
    printf("x2: %d\n", x[2]);
    printf("x3: %d\n", x[3]);
    printf("x4: %d\n", x[4]);
    printf("x5: %d\n", x[5]);
    printf("x7: %d\n", x[7]);
    printf("x9: %d\n", x[9]);
    printf("x10: %d\n", x[10]);
    printf("x11: %d\n", x[11]);
    printf("x12: %d\n", x[12]);
    printf("x13: %d\n", x[13]);
    printf("x14: %d\n", x[14]);
    printf("x15: %d\n", x[15]);
    printf("x16: %d\n", x[16]);
    printf("x17: %d\n", x[17]);
    
    return 0;
}
```

# RV32I Verification Program Table

We used the following link to generate the instruction code for verification of our RV32I CPU architecture :

https://luplab.gitlab.io/rvcodecjs/
| Address | Instruction          | Hex       | Description                         |
|---------|----------------------|-----------|-------------------------------------|
| 0x000   | `nop`                | 0x00000000 | No operation                        |
| 0x004   | `addi x2, x0, 5`     | 0x00500113 | x2 = 5                              |
| 0x008   | `addi x3, x0, 12`    | 0x00C00193 | x3 = 12                             |
| 0x00C   | `addi x7, x3, -9`    | 0xFF718393 | x7 = 12 - 9 = 3                     |
| 0x010   | `or x4, x7, x2`      | 0x0023E233 | x4 = 3 OR 5 = 7                     |
| 0x014   | `and x5, x3, x4`     | 0x0041F2B3 | x5 = 12 AND 7 = 4                   |
| 0x018   | `add x5, x5, x4`     | 0x004282B3 | x5 = 4 + 7 = 11                     |
| 0x01C   | `beq x5, x7, end`    | 0x02728863 | if (11==3)? no branch               |
| 0x020   | `slt x4, x3, x4`     | 0x0041A233 | x4 = (12 < 7) = 0                   |
| 0x024   | `beq x4, x0, around` | 0x00020463 | if (0==0)? branch taken             |
| 0x028   | `addi x5, x0, 0`     | 0x00000293 | skipped (branch taken)              |
| 0x02C   | `slt x4, x7, x2`     | 0x0023A233 | x4 = (3 < 5) = 1                    |
| 0x030   | `add x7, x4, x5`     | 0x005203B3 | x7 = 1 + 11 = 12                    |
| 0x034   | `sub x7, x7, x2`     | 0x402383B3 | x7 = 12 - 5 = 7                     |
| 0x038   | `sw x7, 84(x3)`      | 0x0471AA23 | Mem[24] = 7                   |
| 0x03C   | `lw x2, 96(x0)`      | 0x06002103 | x2 = Mem[24] = 7                    |
| 0x040   | `add x9, x2, x5`     | 0x005104B3 | x9 = 7 + 11 = 18                    |
| 0x044   | `jal x0, 8` (jmp)    | 0x0080006F | Flags Jmp=1 and next_PC=PC+8 instead of PC+4        |
| 0x048   | `addi x2, x0, 1`     | 0x00100113 | skipped (due to jump)               |
| 0x04C   | `add x2, x2, x9`     | 0x00910133 | x2 = 7 + 18 = 25                    |
| 0x050   | `sw x2, 32(x3)`      | 0x0221A023 | Mem[11] = 25                  |
| 0x054   | `addi x10, x0, 5`    | 0x00500513 | x10 = 5                             |
| 0x058   | `addi x11, x0, 0`    | 0x00000593 | x11 = 0                             |
| 0x05C   | `addi x11, x11, 1`   | 0x00158593 | x11 = 1                             |
| 0x060   | `addi x10, x10, -1`  | 0xFFF50513 | x10 = 4                             |
| 0x064   | `beq x10, x0, -16`     | 0xFE0558E3 | if (4==0)? not taken                |
| 0x068   | `sw x11, 100(x0)`     | 0x06B02223 | Mem[25] = 1                       |
| 0x06C   | `lw x12, 100(x0)`    | 0x06402603 | x12 = Mem[25]                      |
| 0x070   | `slli x13,x12,2  `   | 0x00261693 | x13 = 4                             |
| 0x074   | `srli x14,x13,1`     | 0x0016D713 | x14 = 2                             |
| 0x078   | `srai x15,x14,2`     | 0x40275793 | x15 = 0                             |
| 0x07C   | `xor  x16,x13,x13`   | 0x00D6C833 | x16 = 0                             |
| 0x080   | `add x17, x16, x16`  | 0x010808B3 | x17 = 0                             |


---


## 2. Formal Verification module for SingleCycle: `RISCV_SingleCycle_Verification_Properties`

<img width="1839" height="604" alt="image" src="https://github.com/user-attachments/assets/75239031-1cf3-40b3-bae1-b918f882ee2c" />





`timescale 1ns/1ps

module RISCV_Verification (
    input  logic        clk,
    input  logic        reset,
    input  logic [31:0] pc,
    input  logic [31:0] write_back_data,
    input  logic [4:0]  rd_addr,
    input  logic        regWrite,
    input  logic [31:0] data_mem [0:127],
    input  logic [31:0] reg_file [0:31]
);

    logic program_completed;

    always_ff @(posedge clk) begin
        if (reset)
            program_completed <= 1'b0;
        else if (pc == 32'h080)
            program_completed <= 1'b1;
    end

    // ========================================================
    // PROPERTY DEFINITIONS (Golden Table Checks)
    // ========================================================

    //x0 must always be 0

     property p_x0_constant;
        @(posedge clk) disable iff (reset)
            reg_file[0] == 32'd0;
    endproperty

      // PC must always be word-aligned
    property p_pc_aligned;
        @(posedge clk) disable iff (reset)
            (pc[1:0] == 2'b00);
    endproperty

    // NOP
    property p_nop;
        @(posedge clk) disable iff (reset)
        (pc == 32'h000) |->  ##1 (reg_file[0] == 32'd0);
    endproperty

    // Initial setup
    property p_init_x2;
        @(posedge clk) disable iff (reset)
        (pc == 32'h004) |-> ##1 (reg_file[2] == 32'd5);
    endproperty

    property p_init_x3;
        @(posedge clk) disable iff (reset)
        (pc == 32'h008) |->  ##1 (reg_file[3] == 32'd12);
    endproperty

    // Arithmetic
    property p_add_x7;
        @(posedge clk) disable iff (reset)
        (pc == 32'h00C) |-> ##1 (reg_file[7] == 32'd3);
    endproperty

    property p_add_x4;
        @(posedge clk) disable iff (reset)
        (pc == 32'h010) |-> ##1 (reg_file[4] == 32'd7);
    endproperty

    property p_addi_x5;
        @(posedge clk) disable iff (reset)
        (pc == 32'h014) |-> ##1 (reg_file[5] == 32'd4);
    endproperty

    property p_addi2_x5;
        @(posedge clk) disable iff (reset)
        (pc == 32'h018) |-> ##1 (reg_file[5] == 32'd11);
    endproperty

    // Post-branch arithmetic
    property p_postbranch_x4;
        @(posedge clk) disable iff (reset)
        (pc == 32'h02C) |-> ##1 (reg_file[4] == 32'd1);
    endproperty

    property p_postbranch_x7a;
        @(posedge clk) disable iff (reset)
        (pc == 32'h030) |-> ##1 (reg_file[7] == 32'd12);
    endproperty

    property p_postbranch_x7b;
        @(posedge clk) disable iff (reset)
        (pc == 32'h034) |-> ##1 (reg_file[7] == 32'd7);
    endproperty

    // Memory
 property p_store;
    @(posedge clk) disable iff (reset)
    (pc == 32'h038) |-> ##1 (RISCV_SingleCycle.data_mem.mem[24] == 32'd7);
endproperty


    property p_load;
        @(posedge clk) disable iff (reset)
        (pc == 32'h03C) |-> ##1 (reg_file[2] == 32'd7);
    endproperty

    // Jump
    property p_jump_target;
        @(posedge clk) disable iff (reset)
        (pc == 32'h04C) |-> ##1 (reg_file[2] == 32'd25);
    endproperty

    // Store after jump
    property p_store_after_jump;
        @(posedge clk) disable iff (reset)
        (pc == 32'h050) |-> ##1 ( RISCV_SingleCycle.data_mem.mem[11] == 32'd25);
    endproperty

    // Loop
    property p_loop_x10;
        @(posedge clk) disable iff (reset)
        (pc == 32'h054) |-> ##1 (reg_file[10] == 32'd5);
    endproperty

    property p_loop_x11a;
        @(posedge clk) disable iff (reset)
        (pc == 32'h058) |-> ##1 (reg_file[11] == 32'd0);
    endproperty

    property p_loop_x11b;
        @(posedge clk) disable iff (reset)
        (pc == 32'h05C) |-> ##1 (reg_file[11] == 32'd1);
    endproperty

    property p_loop_x10b;
        @(posedge clk) disable iff (reset)
        (pc == 32'h060) |-> ##1 (reg_file[10] == 32'd4);
    endproperty

    property p_loop_store;
        @(posedge clk) disable iff (reset)
        (pc == 32'h068) |-> ##1 ( RISCV_SingleCycle.data_mem.mem[25] == 32'd1);
    endproperty

        // Load from memory
    property p_load_x12;
        @(posedge clk) disable iff (reset)
        (pc == 32'h06C) |-> ##1 (reg_file[12] == 32'd1);
    endproperty

    // Shift left logical immediate
    property p_slli_x13;
        @(posedge clk) disable iff (reset)
        (pc == 32'h070) |-> ##1 (reg_file[13] == 32'd4);
    endproperty

    // Shift right logical immediate
    property p_srli_x14;
        @(posedge clk) disable iff (reset)
        (pc == 32'h074) |-> ##1 (reg_file[14] == 32'd2);
    endproperty

    // Shift right arithmetic immediate
    property p_srai_x15;
        @(posedge clk) disable iff (reset)
        (pc == 32'h078) |-> ##1 (reg_file[15] == 32'd0);
    endproperty

    // XOR result
    property p_xor_x16;
        @(posedge clk) disable iff (reset)
        (pc == 32'h07C) |-> ##1 (reg_file[16] == 32'd0);
    endproperty

    // ADD x17 (NOP-equivalent)
    property p_add_x17;
        @(posedge clk) disable iff (reset)
        (pc == 32'h080) |-> ##1 (reg_file[17] == 32'd0);
    endproperty

    
    
    
    // ========================================================
    // ASSERTIONS
    // ========================================================

   assert property(p_x0_constant)
        else $fatal("x0 register modified illegally! reg_file[0]=%0d", reg_file[0]);


    assert property(p_pc_aligned)
        else $fatal("PC misaligned: 0x%h", pc);

    
    assert property (p_nop)
    else $error("reg_file[0] is %0d when pc==0x000, but expected 0", reg_file[0]);

    assert property (p_init_x2)
        else $error("reg_file[2] is %0d when pc==0x004, but expected 5", reg_file[2]);
    
    assert property (p_init_x3)
        else $error("reg_file[3] is %0d when pc==0x008, but expected 12", reg_file[3]);
    
    assert property (p_add_x7)
        else $error("reg_file[7] is %0d when pc==0x00C, but expected 3", reg_file[7]);
    
    assert property (p_add_x4)
        else $error("reg_file[4] is %0d when pc==0x010, but expected 7", reg_file[4]);
    
    assert property (p_addi_x5)
        else $error("reg_file[5] is %0d when pc==0x014, but expected 4", reg_file[5]);
    
    assert property (p_addi2_x5)
        else $error("reg_file[5] is %0d when pc==0x018, but expected 11", reg_file[5]);
    
    assert property (p_postbranch_x4)
        else $error("reg_file[4] is %0d when pc==0x02C, but expected 1", reg_file[4]);
    
    assert property (p_postbranch_x7a)
        else $error("reg_file[7] is %0d when pc==0x030, but expected 12", reg_file[7]);
    
    assert property (p_postbranch_x7b)
        else $error("reg_file[7] is %0d when pc==0x034, but expected 7", reg_file[7]);
    
    assert property (p_store)
        else $error("data_mem[24] is %0d when pc==0x038, but expected 7",  RISCV_SingleCycle.data_mem.mem[24]);
    
    assert property (p_load)
        else $error("reg_file[2] is %0d when pc==0x03C, but expected 7", reg_file[2]);
    
    assert property (p_jump_target)
        else $error("reg_file[2] is %0d when pc==0x04C, but expected 25", reg_file[2]);
    
    assert property (p_store_after_jump)
        else $error("data_mem[11] is %0d when pc==0x050, but expected 25",  RISCV_SingleCycle.data_mem.mem[11]);
    
    assert property (p_loop_x10)
        else $error("reg_file[10] is %0d when pc==0x054, but expected 5", reg_file[10]);
    
    assert property (p_loop_x11a)
        else $error("reg_file[11] is %0d when pc==0x058, but expected 0", reg_file[11]);
    
    assert property (p_loop_x11b)
        else $error("reg_file[11] is %0d when pc==0x05C, but expected 1", reg_file[11]);
    
     assert property (p_loop_x10b)
        else $error("reg_file[10] is %0d when pc==0x060, but expected 4", reg_file[10]);



    assert property (p_loop_store)
    else begin
     
        $error("data_mem[25] is %0d when pc==0x068, but expected 1", 
               RISCV_SingleCycle.data_mem.mem[25]);
       
    end


    assert property (p_load_x12)
        else $error("reg_file[12] is %0d when pc==0x06C, but expected 1", reg_file[12]);

    assert property (p_slli_x13)
        else $error("reg_file[13] is %0d when pc==0x070, but expected 4", reg_file[13]);

    assert property (p_srli_x14)
        else $error("reg_file[14] is %0d when pc==0x074, but expected 2", reg_file[14]);

    assert property (p_srai_x15)
        else $error("reg_file[15] is %0d when pc==0x078, but expected 0", reg_file[15]);

    assert property (p_xor_x16)
        else $error("reg_file[16] is %0d when pc==0x07C, but expected 0", reg_file[16]);

    assert property (p_add_x17)
        else $error("reg_file[17] is %0d when pc==0x080, but expected 0", reg_file[17]);


    // ========================================================
    // COMPLETION MESSAGE
    // ========================================================
    always_ff @(posedge clk) begin
        if (program_completed) begin
            $display("✓ Program completed at PC=0x%h", pc);
        end
    end

endmodule

---



3. Testbench_SingleCycle_RISCV: `RISV_tb`

```verilog
`timescale 1ns / 1ps
module RISV_tb;

    // Top-level stimulus signals
    logic clk;
    logic reset;
    logic [31:0] write_back_data;
    logic start;
    logic [31:0] Imem_write_instr;
    logic Imem_write_en;
    logic Up, Down;
    logic [31:0] pc;

    // Instantiate the DUT (match ports in RISCV_SingleCycle)
    RISCV_SingleCycle dut (
        .clk(clk),
        .reset(reset),
        .start(start),
        .Imem_write_instr(Imem_write_instr),
        .Imem_write_en(Imem_write_en),
        .Up(Up),
        .Down(Down),
        .pc(pc),
        .write_back_data(write_back_data)
    );

    // Instantiate the verification module.
    // Note: verifier reads some DUT internals hierarchically (reg file, data mem).
    RISCV_Verification verifier (
        .clk(clk),
        .reset(reset),
        .pc(dut.pc),                       // pc is an output port of DUT
        .write_back_data(dut.write_back_data),
        .rd_addr( 5'd0 ),
        .regWrite( 1'b0 ),
        .data_mem(dut.data_mem.mem),       // hierarchical: DataMem instance must expose `mem`
        .reg_file(dut.reg_file.regs)       // hierarchical: RegFile instance must expose `regs`
    );

    // Clock generation
    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk; // 100 MHz -> 10 ns period (for example)
    end

    // Load instructions into instruction memory (hierarchical access)
    initial begin
        // Defensive init in case mem size > program size
        for (int i = 0; i < 256; i++) begin
            dut.instr_mem.mem[i] = 32'h00000000;
        end

        // Program (word-addressed mem indices)
        dut.instr_mem.mem[0]  = 32'h00000000; // 0x000: nop
        dut.instr_mem.mem[1]  = 32'h00500113; // 0x004: addi x2, x0, 5
        dut.instr_mem.mem[2]  = 32'h00C00193; // 0x008: addi x3, x0, 12
        dut.instr_mem.mem[3]  = 32'hFF718393; // 0x00C: addi x7, x3, -9
        dut.instr_mem.mem[4]  = 32'h0023E233; // 0x010: or x4, x7, x2
        dut.instr_mem.mem[5]  = 32'h0041F2B3; // 0x014: and x5, x3, x4
        dut.instr_mem.mem[6]  = 32'h004282B3; // 0x018: add x5, x5, x4
        dut.instr_mem.mem[7]  = 32'h02728863; // 0x01C: beq x5, x7, end
        dut.instr_mem.mem[8]  = 32'h0041A233; // 0x020: slt x4, x3, x4
        dut.instr_mem.mem[9]  = 32'h00020463; // 0x024: beq x4, x0, around
        dut.instr_mem.mem[10] = 32'h00000293; // 0x028: addi x5, x0, 0
        dut.instr_mem.mem[11] = 32'h0023A233; // 0x02C: slt x4, x7, x2
        dut.instr_mem.mem[12] = 32'h005203B3; // 0x030: add x7, x4, x5
        dut.instr_mem.mem[13] = 32'h402383B3; // 0x034: sub x7, x7, x2
        dut.instr_mem.mem[14] = 32'h0471AA23; // 0x038: sw x7, 84(x3)
        dut.instr_mem.mem[15] = 32'h06002103; // 0x03C: lw x2, 96(x0)
        dut.instr_mem.mem[16] = 32'h005104B3; // 0x040: add x9, x2, x5
        dut.instr_mem.mem[17] = 32'h0080006F; // 0x044: jal x0, 8 (jmp)
        dut.instr_mem.mem[18] = 32'h00100113; // 0x048: addi x2, x0, 1
        dut.instr_mem.mem[19] = 32'h00910133; // 0x04C: add x2, x2, x9
        dut.instr_mem.mem[20] = 32'h0221A023; // 0x050: sw x2, 32(x3)
        dut.instr_mem.mem[21] = 32'h00500513; // 0x054: addi x10, x0, 5
        dut.instr_mem.mem[22] = 32'h00000593; // 0x058: addi x11, x0, 0
        dut.instr_mem.mem[23] = 32'h00158593; // 0x05C: addi x11, x11, 1
        dut.instr_mem.mem[24] = 32'hFFF50513; // 0x060: addi x10, x10, -1
        dut.instr_mem.mem[25] = 32'hFE0558E3; // 0x064: beq x10, x0, -16
        dut.instr_mem.mem[26] = 32'h06B02223; // 0x068: sw x11, 100(x0)
        dut.instr_mem.mem[27] = 32'h06402603; // 0x06C: lw x12, 100(x0)
        dut.instr_mem.mem[28] = 32'h00261693; // 0x070: slli x13,x12,2
        dut.instr_mem.mem[29] = 32'h0016D713; // 0x074: srli x14,x13,1
        dut.instr_mem.mem[30] = 32'h40275793; // 0x078: srai x15,x14,2
        dut.instr_mem.mem[31] = 32'h00D6C833; // 0x07C: xor x16,x13,x13
        dut.instr_mem.mem[32] = 32'h010808B3; // 0x080: add x17,x16,x16
    end

    // Test stimulus & checks
    initial begin
        $timeformat(-9, 2, " ns", 20);

        // default inputs
        start = 1'b0;
        Imem_write_instr = 32'b0;
        Imem_write_en = 1'b0;
        Up = 1'b0; Down = 1'b0;
        reset = 1'b1;         // assert reset first
        @(posedge clk);
        @(posedge clk);
        reset = 1'b0;         // deassert reset -> start running
        start = 1'b1;

        // Wait until verifier signals program completion (hierarchical reference)
        wait (verifier.program_completed);

        // Give one more cycle for final writes to settle
        @(posedge clk);

       
        $finish;
    end

endmodule

```

---

This `.md` file contains the **verification module** with property checks for registers, memory, arithmetic, branches, and loops, along with a **testbench** that drives the CPU and monitors program execution. The properties are asserted automatically during simulation, and final checks are displayed once the program completes.
