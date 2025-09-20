`timescale 1ns / 1ps
module RISV_tb;
    logic clk;
    logic reset;
    logic [31:0] write_back_data;
    logic start;
    logic [31:0] Imem_write_instr;
    logic Imem_write_en;
    logic Up;
    logic Down;
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

    // Clock generation
    initial begin
        clk = 1;
        forever #5 clk = ~clk;
    end

    initial begin
        $dumpfile("simulation_output.vcd");
        $dumpvars;

        $timeformat(-9, 2, " ns", 20);
        start = 0;
        Imem_write_instr = 32'b0;
        Imem_write_en = 0;
        Up = 0;
        Down = 0;
        reset = 0;

        @(posedge clk);
        reset = 1;

        @(posedge clk);
        reset = 0;
        start = 1;

        repeat (32) begin
            @(posedge clk);
        end
        start = 0;
        Imem_write_instr = 32'h00AE0E13; 
        Up = 1;

        repeat (3) begin
            @(posedge clk);
        end
        Imem_write_en = 1;
        
        @(posedge clk);
        Imem_write_en = 0;
        Up = 0;
        Down = 1;

        repeat (4) begin
            @(posedge clk);
        end
        Down = 0;
        start = 1;
        repeat (10) begin
            @(posedge clk);
        end
        $finish;
        $stop;
    end
endmodule