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

//    assert property (p_loop_store)
//        else $error("data_mem[25] is %0d when pc==0x068, but expected 1", data_mem[25]);


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
