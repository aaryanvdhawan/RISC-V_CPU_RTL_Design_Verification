module instruction_mem  (
    input  logic [31:0]            pc,         // Address from PC
    input  logic                   clk,        // Clock signal
    input  logic                   reset,
    input  logic [31:0]            write_instr,
    input  logic                   write_en,
    output logic [31:0]            instr_out   // Instruction at PC
);
    // 64 x 32-bit instruction memory
    logic [31:0] mem [0:63]; 
    
    // Initial block to hardcode instructions
    // initial begin
    //     // Default memory initialization
    //     for (int i = 0; i < 64; i++) begin
    //         mem[i] = 32'b0;
    //     end

    //     // mem[0] = 0
    //     mem[0]  = 32'h00000000;

    //     // Hardcoded instructions
    //     mem[0]  = 32'h00000000;   // 0x000: nop
    //     mem[1]  = 32'h00500113;   // 0x004: addi x2, x0, 5
    //     mem[2]  = 32'h00C00193;   // 0x008: addi x3, x0, 12
    //     mem[3]  = 32'hFF718393;   // 0x00C: addi x7, x3, -9
    //     mem[4]  = 32'h0023E233;   // 0x010: or x4, x7, x2
    //     mem[5]  = 32'h0041F2B3;   // 0x014: and x5, x3, x4
    //     mem[6]  = 32'h004282B3;   // 0x018: add x5, x5, x4
    //     mem[7]  = 32'h02728863;   // 0x01C: beq x5, x7, end (not taken)
    //     mem[8]  = 32'h0041A233;   // 0x020: slt x4, x3, x4
    //     mem[9]  = 32'h00020463;   // 0x024: beq x4, x0, around (taken)
    //     mem[10] = 32'h00000293;   // 0x028: addi x5, x0, 0 (skipped due to branch)
    //     mem[11] = 32'h0023A233;   // 0x02C: slt x4, x7, x2
    //     mem[12] = 32'h005203B3;   // 0x030: add x7, x4, x5
    //     mem[13] = 32'h402383B3;   // 0x034: sub x7, x7, x2
    //     mem[14] = 32'h0471AA23;   // 0x038: sw x7, 84(x3)
    //     mem[15] = 32'h06002103;   // 0x03C: lw x2, 96(x0)
    //     mem[16] = 32'h005104B3;   // 0x040: add x9, x2, x5
    //     mem[17] = 32'h0080006F;   // 0x044: jmp 0x04C (jump immediate = 8)
    //     mem[18] = 32'h00100113;   // 0x048: addi x2, x0, 1 (skipped due to jump)
    //     mem[19] = 32'h00910133;   // 0x04C: add x2, x2, x9
    //     mem[20] = 32'h0221A023;   // 0x050: sw x2, 32(x3)
    //     mem[21] = 32'h00500513;   // 0x054: addi x10, x0, 5
    //     mem[22] = 32'h00000593;   // 0x058: addi x11, x0, 0
    //     mem[23] = 32'h00158593;   // 0x05C: addi x11, x11, 1
    //     mem[24] = 32'hFFF50513;   // 0x060: addi x10, x10, -1
    //     mem[25] = 32'hFE0558E3;   // 0x064: beq x10, x0, ? (not taken here)
    //     mem[26] = 32'h06B02223;   // 0x068: sw x11, 44(x0)
    //     mem[27] = 32'h06402603;   // 0x06C: lw x12, 100(x0)
    //     mem[28] = 32'h00261693;   // 0x070: addi x13, x12, 2
    //     mem[29] = 32'h0016D713;   // 0x074: addi x14, x13, 1
    //     mem[30] = 32'h40275793;   // 0x078: sub x15, x14, x2
    //     mem[31] = 32'h00D6C833;   // 0x07C: add x16, x13, x13
    //     mem[32] = 32'h010808B3;   // 0x080: add x17, x16, x16
    //     // Remaining memory initialized to 0
    // end

    // Asynchronous read
    assign instr_out = mem[pc[31:2]]; // Word-aligned access

    // Synchronous write
    always_ff @(posedge clk) begin
        if (reset) begin
            // mem[0] = 0
            mem[0]  <= 32'h00000000;
            // Hardcoded instructions
            mem[0]  <= 32'h00000000;   // 0x000: nop
            mem[1]  <= 32'h00500113;   // 0x004: addi x2, x0, 5
            mem[2]  <= 32'h00C00193;   // 0x008: addi x3, x0, 12
            mem[3]  <= 32'hFF718393;   // 0x00C: addi x7, x3, -9
            mem[4]  <= 32'h0023E233;   // 0x010: or x4, x7, x2
            mem[5]  <= 32'h0041F2B3;   // 0x014: and x5, x3, x4
            mem[6]  <= 32'h004282B3;   // 0x018: add x5, x5, x4
            mem[7]  <= 32'h02728863;   // 0x01C: beq x5, x7, end (not taken)
            mem[8]  <= 32'h0041A233;   // 0x020: slt x4, x3, x4
            mem[9]  <= 32'h00020463;   // 0x024: beq x4, x0, around (taken)
            mem[10] <= 32'h00000293;   // 0x028: addi x5, x0, 0 (skipped due to branch)
            mem[11] <= 32'h0023A233;   // 0x02C: slt x4, x7, x2
            mem[12] <= 32'h005203B3;   // 0x030: add x7, x4, x5
            mem[13] <= 32'h402383B3;   // 0x034: sub x7, x7, x2
            mem[14] <= 32'h0471AA23;   // 0x038: sw x7, 84(x3)
            mem[15] <= 32'h06002103;   // 0x03C: lw x2, 96(x0)
            mem[16] <= 32'h005104B3;   // 0x040: add x9, x2, x5
            mem[17] <= 32'h0080006F;   // 0x044: jmp 0x04C (jump immediate = 8)
            mem[18] <= 32'h00100113;   // 0x048: addi x2, x0, 1 (skipped due to jump)
            mem[19] <= 32'h00910133;   // 0x04C: add x2, x2, x9
            mem[20] <= 32'h0221A023;   // 0x050: sw x2, 32(x3)
            mem[21] <= 32'h00500513;   // 0x054: addi x10, x0, 5
            mem[22] <= 32'h00000593;   // 0x058: addi x11, x0, 0
            mem[23] <= 32'h00158593;   // 0x05C: addi x11, x11, 1
            mem[24] <= 32'hFFF50513;   // 0x060: addi x10, x10, -1
            mem[25] <= 32'hFE0558E3;   // 0x064: beq x10, x0, ? (not taken here)
            mem[26] <= 32'h06B02223;   // 0x068: sw x11, 44(x0)
            mem[27] <= 32'h06402603;   // 0x06C: lw x12, 100(x0)
            mem[28] <= 32'h00261693;   // 0x070: addi x13, x12, 2
            mem[29] <= 32'h0016D713;   // 0x074: addi x14, x13, 1
            mem[30] <= 32'h40275793;   // 0x078: sub x15, x14, x2
            mem[31] <= 32'h00D6C833;   // 0x07C: add x16, x13, x13
            mem[32] <= 32'h010808B3;   // 0x080: add x17, x16, x16
        // Remaining memory initialized to 0
            mem[33] <= 32'h00000000;
            mem[34] <= 32'h00000000;
            mem[35] <= 32'h00000000;
            mem[36] <= 32'h00000000;
            mem[37] <= 32'h00000000;
            mem[38] <= 32'h00000000;
            mem[39] <= 32'h00000000;
            mem[40] <= 32'h00000000;
            mem[41] <= 32'h00000000;
            mem[42] <= 32'h00000000;
            mem[43] <= 32'h00000000;
            mem[44] <= 32'h00000000;
            mem[45] <= 32'h00000000;
            mem[46] <= 32'h00000000;
            mem[47] <= 32'h00000000;
            mem[48] <= 32'h00000000;
            mem[49] <= 32'h00000000;
            mem[50] <= 32'h00000000;
            mem[51] <= 32'h00000000;
            mem[52] <= 32'h00000000;
            mem[53] <= 32'h00000000;
            mem[54] <= 32'h00000000;
            mem[55] <= 32'h00000000;
            mem[56] <= 32'h00000000;
            mem[57] <= 32'h00000000;
            mem[58] <= 32'h00000000;
            mem[59] <= 32'h00000000;
            mem[60] <= 32'h00000000;
            mem[61] <= 32'h00000000;
            mem[62] <= 32'h00000000;
            mem[63] <= 32'h00000000;
        end
        if (write_en) begin
            mem[pc[31:2]] <= write_instr;
        end
    end

endmodule