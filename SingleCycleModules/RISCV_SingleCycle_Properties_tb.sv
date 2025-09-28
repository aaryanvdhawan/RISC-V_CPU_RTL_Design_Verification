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
