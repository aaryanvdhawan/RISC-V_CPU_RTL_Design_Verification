`timescale 1ns / 1ps
module RISV_tb;
    logic clk;
    logic reset;
    logic [31:0] write_back_data;
    logic start;

    // Instantiate the DUT
    RISCV_Top dut (
        .clk(clk),
        .reset(reset),
        .start(start), 
        .write_back_data(write_back_data)
    );

    // Clock generation
    initial begin
        clk = 1;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
        start = 0;
        reset = 1;
        #10;
        reset = 0;
        @(posedge clk);
        
        start = 1;
        @(posedge clk);
        start = 0;
        @(posedge clk);
        @(posedge clk);
        start = 1;
        @(posedge clk);
        #50;
        $finish;
        $stop;
    end

endmodule