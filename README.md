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
