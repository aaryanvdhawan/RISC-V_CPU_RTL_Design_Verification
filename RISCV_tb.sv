`timescale 1ns / 1ps
module RISV_tb;
    logic clk;
    logic reset;
    logic [9:0] sw;
    logic [31:0] write_back_data;

    // Instantiate the DUT
    RISCV_Top dut (
        .clk(clk),
        .reset(reset),
        .sw(sw),
        .write_back_data(write_back_data)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
        reset = 1;
        sw = 10'b0;
        #10;
        reset = 0;

        // Test case in instruction memory

        #100;
        $finish;
        $stop;
    end

endmodule