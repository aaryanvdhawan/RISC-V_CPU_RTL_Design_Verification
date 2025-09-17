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