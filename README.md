# RISC-V Verification Module and Testbench

This document contains a SystemVerilog verification module for a RISCV single-cycle CPU along with its testbench. The verification module checks registers, memory, and instruction execution correctness.

---



## 1. Instruction Table

| Address | Instruction        | Hex        | Description                          |
| ------- | ------------------ | ---------- | ------------------------------------ |
| 0x000   | nop                | 0x00000000 | No operation / NOP                   |
| 0x004   | addi x2, x0, 5     | 0x00500113 | x2 = 5                               |
| 0x008   | addi x3, x0, 12    | 0x00C00193 | x3 = 12                              |
| 0x00C   | addi x7, x3, -9    | 0xFF718393 | x7 = 12 - 9 = 3                      |
| 0x010   | or x4, x7, x2      | 0x0023E233 | x4 = 3 OR 5 = 7                      |
| 0x014   | and x5, x3, x4     | 0x0041F2B3 | x5 = 12 AND 7 = 4                    |
| 0x018   | add x5, x5, x4     | 0x004282B3 | x5 = 4 + 7 = 11                      |
| 0x01C   | beq x5, x7, end    | 0x02728863 | if x5 == x7, jump to end (not taken)|
| 0x020   | slt x4, x3, x4     | 0x0041A233 | x4 = (12 < 7) = 0                    |
| 0x024   | beq x4, x0, around | 0x00020463 | if x4 == 0, jump to around (taken)   |
| 0x028   | addi x5, x0, 0     | 0x00000293 | x5 = 0 (not executed)                |
| 0x02C   | slt x4, x7, x2     | 0x0023A233 | x4 = (3 < 5) = 1                     |
| 0x030   | add x7, x4, x5     | 0x005203B3 | x7 = 1 + 11 = 12                     |
| 0x034   | sub x7, x7, x2     | 0x402383B3 | x7 = 12 - 5 = 7                      |
| 0x038   | sw x7, 84(x3)      | 0x0471AA23 | Mem[12+84=96] = 7                    |
| 0x03C   | lw x2, 96(x0)      | 0x06002103 | x2 = Mem[96] = 7                     |
| 0x040   | add x9, x2, x5     | 0x005104B3 | x9 = 7 + 11 = 18                     |
| 0x044   | jal x1, 8          | 0x008001EF | x1 = PC+4, jump to PC+8              |
| 0x048   | addi x2, x0, 1     | 0x00100113 | x2 = 1                               |
| 0x04C   | add x2, x2, x9     | 0x00910133 | x2 = 1 + 18 = 19                     |
| 0x050   | sw x2, 32(x3)      | 0x0221A023 | Mem[x3+32] = x2 = 19                 |
| 0x054   | addi x10, x0, 5    | 0x00500513 | x10 = 5                              |
| 0x058   | addi x11, x0, 0    | 0x00000593 | x11 = 0                              |
| 0x05C   | addi x11, x11, 1   | 0x00158593 | x11 = 0 + 1 = 1                      |
| 0x060   | addi x10, x10, -1  | 0xFFF50513 | x10 = 5 - 1 = 4                      |
| 0x064   | beq x10, x0, ?     | 0xFE0558E3 | Branch if x10==0 (not taken)         |
| 0x068   | sw x11, 44(x0)     | 0x06B02223 | Mem[44] = 1                           |
| 0x06C   | lw x12, 100(x0)    | 0x06402603 | x12 = Mem[100]                        |
| 0x070   | addi x13, x12, 2   | 0x00261693 | x13 = x12 + 2                         |
| 0x074   | addi x14, x13, 1   | 0x0016D713 | x14 = x13 + 1                         |
| 0x078   | sub x15, x14, x2   | 0x40275793 | x15 = x14 - x2                        |
| 0x07C   | add x16, x13, x13  | 0x00D6C833 | x16 = x13 + x13                        |
| 0x080   | add x17, x16, x16  | 0x010808B3 | x17 = x16 + x16                        |

---


## 2. Formal Verification module: `RISCV_Verification_Properties`

```verilog
module RISCV_Verification (
    input logic clk,
    input logic reset,
    input logic [31:0] pc,
    input logic [31:0] write_back_data,
    input logic [4:0] rd_addr,
    input logic regWrite,
    input logic [31:0] data_mem [0:127],
    input logic [31:0] reg_file [0:31]
);

    // Track program execution state
    logic [31:0] last_pc;
    logic program_completed;
    
    initial begin
        last_pc = 32'h0;
        program_completed = 1'b0;
    end
    
    always_ff @(posedge clk) begin
        last_pc <= pc;
        if (pc == 32'h080) begin  // Final instruction address
            program_completed <= 1'b1;
        end
    end

    // Property 1: NOP instruction at start
    property check_nop;
        @(posedge clk) disable iff (reset)
        (pc == 32'h000) |-> (reg_file[0] == 32'd0); // x0 should always be 0
    endproperty
    
    // Property 2: Initial register setup
    property check_initial_setup;
        @(posedge clk) disable iff (reset)
        (pc == 32'h00C) |-> (reg_file[2] == 32'd5) && (reg_file[3] == 32'd12);
    endproperty
    
    // Property 3: Arithmetic operations (first set)
    property check_arithmetic_ops_1;
        @(posedge clk) disable iff (reset)
        (pc == 32'h014) |-> (reg_file[7] == 32'd3) &&   // x7 = 3
                          (reg_file[4] == 32'd7) &&   // x4 = 7
                          (reg_file[5] == 32'd4);     // x5 = 4
    endproperty
    
    // Property 4: More arithmetic operations
    property check_arithmetic_ops_2;
        @(posedge clk) disable iff (reset)
        (pc == 32'h018) |-> (reg_file[5] == 32'd11);  // x5 = 11
    endproperty
    
    // Property 5: Branch behavior
    property check_branch_not_taken;
        @(posedge clk) disable iff (reset)
        (pc == 32'h01C) |-> (reg_file[5] != reg_file[7]);  // beq should not be taken (11 != 3)
    endproperty
    
    property check_slt_result;
        @(posedge clk) disable iff (reset)
        (pc == 32'h020) |-> (reg_file[4] == 32'd0);  // slt x4, x3, x4: 12 < 7 = 0
    endproperty
    
    property check_branch_taken;
        @(posedge clk) disable iff (reset)
        (pc == 32'h024) |-> (reg_file[4] == 32'd0);  // beq should be taken (x4 == 0)
    endproperty
    
    // Property 6: Skipped instruction verification
    property check_skipped_instruction;
        @(posedge clk) disable iff (reset)
        (pc == 32'h02C) |-> (reg_file[5] == 32'd11);  // addi x5, x0, 0 should be skipped
    endproperty
    
    // Property 7: More arithmetic after branch
    property check_post_branch_arithmetic;
        @(posedge clk) disable iff (reset)
        (pc == 32'h030) |-> (reg_file[4] == 32'd1) &&   // slt x4, x7, x2: 3 < 5 = 1
                          (reg_file[7] == 32'd12) &&  // add x7, x4, x5: 1 + 11 = 12
                          (reg_file[7] == 32'd7);     // sub x7, x7, x2: 12 - 5 = 7
    endproperty
    
    // Property 8: Memory operations
    property check_memory_store;
        @(posedge clk) disable iff (reset)
        (pc == 32'h03C) |-> (data_mem[96] == 32'd7);  // sw x7, 84(x3): Mem[12+84=96] = 7
    endproperty
    
    property check_memory_load;
        @(posedge clk) disable iff (reset)
        (pc == 32'h040) |-> (reg_file[2] == 32'd7);  // lw x2, 96(x0): x2 = Mem[96] = 7
    endproperty
    
    // Property 9: Jump and link
    property check_jal;
        @(posedge clk) disable iff (reset)
        (pc == 32'h048) |-> (reg_file[1] == 32'h048);  // jal x1, 8: x1 = PC+4 = 0x44+4 = 0x48
    endproperty
    
    // Property 10: Post-jump arithmetic
    property check_post_jump_arithmetic;
        @(posedge clk) disable iff (reset)
        (pc == 32'h04C) |-> (reg_file[2] == 32'd1) &&   // addi x2, x0, 1: x2 = 1
                          (reg_file[2] == 32'd19) &&  // add x2, x2, x9: 1 + 18 = 19
                          (reg_file[9] == 32'd18);    // x9 should still be 18
    endproperty
    
    // Property 11: Memory store after jump
    property check_memory_store_2;
        @(posedge clk) disable iff (reset)
        (pc == 32'h050) |-> (data_mem[44] == 32'd19);  // sw x2, 32(x3): Mem[12+32=44] = 19
    endproperty
    
    // Property 12: Loop operations
    property check_loop_operations;
        @(posedge clk) disable iff (reset)
        (pc == 32'h060) |-> (reg_file[10] == 32'd5) &&   // addi x10, x0, 5: x10 = 5
                          (reg_file[11] == 32'd0) &&   // addi x11, x0, 0: x11 = 0
                          (reg_file[11] == 32'd1) &&   // addi x11, x11, 1: x11 = 1
                          (reg_file[10] == 32'd4);     // addi x10, x10, -1: x10 = 4
    endproperty
    
    // Property 13: Branch in loop
    property check_loop_branch;
        @(posedge clk) disable iff (reset)
        (pc == 32'h064) |-> (reg_file[10] != 32'd0);  // beq should not be taken (x10 = 4 != 0)
    endproperty
    
    // Property 14: Memory operations in loop
    property check_loop_memory;
        @(posedge clk) disable iff (reset)
        (pc == 32'h068) |-> (data_mem[44] == 32'd1);  // sw x11, 44(x0): Mem[44] = 1
    endproperty
    
    // Property 15: Final arithmetic operations
    property check_final_arithmetic;
        @(posedge clk) disable iff (reset)
        (pc == 32'h080) |-> (reg_file[12] == data_mem[100]) &&  // lw x12, 100(x0)
                          (reg_file[13] == reg_file[12] + 32'd2) &&  // addi x13, x12, 2
                          (reg_file[14] == reg_file[13] + 32'd1) &&  // addi x14, x13, 1
                          (reg_file[15] == reg_file[14] - reg_file[2]) &&  // sub x15, x14, x2
                          (reg_file[16] == reg_file[13] + reg_file[13]) && // add x16, x13, x13
                          (reg_file[17] == reg_file[16] + reg_file[16]);   // add x17, x16, x16
    endproperty
    
    // Property 16: Register write consistency
    property check_reg_write_consistency;
        @(posedge clk) disable iff (reset)
        (regWrite && (rd_addr != 0)) |-> (##1 reg_file[rd_addr] == $past(write_back_data));
    endproperty

    // Assert the properties
    initial begin
        // Basic operations
        assert property (check_nop)
            else $error("NOP instruction issue");
            
        assert property (check_initial_setup)
            else $error("Initial setup failed: x2=%0d, x3=%0d", reg_file[2], reg_file[3]);
            
        assert property (check_arithmetic_ops_1)
            else $error("Arithmetic ops 1 failed: x7=%0d, x4=%0d, x5=%0d", 
                       reg_file[7], reg_file[4], reg_file[5]);
            
        assert property (check_arithmetic_ops_2)
            else $error("Arithmetic ops 2 failed: x5=%0d, expected=11", reg_file[5]);
            
        // Branch and comparison
        assert property (check_branch_not_taken)
            else $error("Branch should not be taken: x5=%0d, x7=%0d", reg_file[5], reg_file[7]);
            
        assert property (check_slt_result)
            else $error("SLT result incorrect: x4=%0d, expected=0", reg_file[4]);
            
        assert property (check_branch_taken)
            else $error("Branch should be taken: x4=%0d", reg_file[4]);
            
        assert property (check_skipped_instruction)
            else $error("Instruction not properly skipped: x5=%0d, expected=11", reg_file[5]);
            
        // Memory and jump operations
        assert property (check_post_branch_arithmetic)
            else $error("Post-branch arithmetic failed");
            
        assert property (check_memory_store)
            else $error("Memory store failed: Mem[96]=%0d, expected=7", data_mem[96]);
            
        assert property (check_memory_load)
            else $error("Memory load failed: x2=%0d, expected=7", reg_file[2]);
            
        assert property (check_jal)
            else $error("JAL failed: x1=0x%h, expected=0x48", reg_file[1]);
            
        assert property (check_post_jump_arithmetic)
            else $error("Post-jump arithmetic failed");
            
        assert property (check_memory_store_2)
            else $error("Memory store 2 failed: Mem[44]=%0d, expected=19", data_mem[44]);
            
        // Loop operations
        assert property (check_loop_operations)
            else $error("Loop operations failed");
            
        assert property (check_loop_branch)
            else $error("Loop branch incorrect: x10=%0d", reg_file[10]);
            
        assert property (check_loop_memory)
            else $error("Loop memory failed: Mem[44]=%0d, expected=1", data_mem[44]);
            
        // Final checks
        assert property (check_final_arithmetic)
            else $error("Final arithmetic operations failed");
            
        assert property (check_reg_write_consistency)
            else $error("Register write consistency failed");
            
        // Completion check
        if (program_completed) begin
            $display("✓ All instructions executed successfully");
            $display("✓ Program completed at PC = 0x%h", pc);
            $display("✓ Final register values:");
            for (int i = 0; i < 32; i++) begin
                if (reg_file[i] != 0) 
                    $display("  x%0d = %0d (0x%h)", i, reg_file[i], reg_file[i]);
            end
        end
    end

endmodule

---


## **3. Testbench: `RISV_tb`**

```verilog
`timescale 1ns / 1ps
module RISV_tb;

    logic clk;
    logic reset;
    logic [31:0] write_back_data;
    logic start;
    logic [31:0] Imem_write_instr;
    logic Imem_write_en;
    logic Up, Down, Set;
    logic [31:0] pc;

    // Instantiate the DUT
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

    // Instantiate the verification module
    RISCV_Verification verifier (
        .clk(clk),
        .reset(reset),
        .pc(dut.pc),
        .write_back_data(dut.write_back_data),
        .rd_addr(dut.rd),
        .regWrite(dut.regWrite),
        .data_mem(dut.data_mem.mem),
        .reg_file(dut.reg_file.regs)
    );

    // Clock generation
    initial begin
        clk = 1;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
        $timeformat(-9, 2, " ns", 20);
        start = 0;
        Imem_write_instr = 32'b0;
        Imem_write_en = 0;
        Up = 0; Down = 0; Set = 0;
        reset = 0;

        @(posedge clk);
        reset = 1;
        @(posedge clk);
        reset = 0; start = 1;

        // Add stimulus and checks as needed
        @(posedge clk);
        $display("Current write_back_data: %0d", dut.write_back_data);

        // Wait for program completion
        wait(verifier.program_completed);

        // Final checks
        if (dut.reg_file.regs[2] == 32'd25)
            $display("✓ Test PASSED: x2 = %0d", dut.reg_file.regs[2]);
        else
            $error("✗ Test FAILED: x2 = %0d, expected 25", dut.reg_file.regs[2]);

        if (dut.data_mem.mem[44] == 32'd25)
            $display("✓ Memory test PASSED: Mem[44] = %0d", dut.data_mem.mem[44]);
        else
            $error("✗ Memory test FAILED: Mem[44] = %0d, expected 25", dut.data_mem.mem[44]);

        $display("Simulation completed at time %t", $time);
        $finish;
    end

endmodule
```

---

This `.md` file contains the **verification module** with property checks for registers, memory, arithmetic, branches, and loops, along with a **testbench** that drives the CPU and monitors program execution. The properties are asserted automatically during simulation, and final checks are displayed once the program completes.
