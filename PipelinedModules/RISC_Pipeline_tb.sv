`timescale 1ns / 1ps
module RISC_Pipeline_tb;
    // Top-level stimulus signals
    logic clk;
    logic reset;
    logic start;
    logic [4:0] SW;
    logic [15:0] OUT;

    // Instantiate the DUT (match ports in RISCV_Pipeline)
    RISCV_Pipeline dut (
        .clk(clk),
        .reset(reset),
        .start(start),
        .SW(SW),
        .OUT(OUT)
    );

    // Clock generation
    initial begin
        clk = 1'b0;
        forever #5 clk = ~clk; // 100 MHz -> 10 ns period (for example)
    end

    // Stimulus process
    initial begin
        // Initialize signals
        $dumpfile("simulation_output.vcd");
        $dumpvars;

        $timeformat(-9, 2, " ns", 20);
        reset = 0;
        start = 0;
        SW = 5'b00000; // Change this to select different registers to display

        @(posedge clk);
        reset = 1;

        @(posedge clk);
        reset = 0;
        start = 1;

        repeat (40) begin
            @(posedge clk);
        end
        start = 0;
        $finish;
        $stop;
    end

endmodule
