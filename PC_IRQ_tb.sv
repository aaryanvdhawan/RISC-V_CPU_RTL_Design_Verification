`timescale 1ns / 1ps
module PC_IRQ();
    
    logic clk;
    logic reset;
    logic irq;
    logic jump;
    logic [31:0] pc_target;
    logic branch;
    logic zero_flag;
    logic up;
    logic down;
    logic [31:0] pc;
    logic [31:0] instr_in;
    logic [31:0] instr_out;

    PC_Counter_IRQ pc_counter_irq (
        .clk(clk),
        .reset(reset),
        .irq(irq),
        .jump(jump),
        .pc_target(pc_target),
        .branch(branch),
        .zero_flag(zero_flag),
        .up(up),
        .down(down),
        .pc(pc)
    );

    IMEM imem (
        .pc(pc),
        .clk(clk),
        .reset(reset),
        .instr_in(instr_in),
        .write_enable(irq),
        .instr_out(instr_out)
    );

    always begin
        clk = 1;
        forever #5 clk = ~clk; // 10 ns clock period
    end

    initial begin
        // Initialize signals
        reset = 1;
        irq = 0;
        jump = 0;
        pc_target = 32'h00000000;
        branch = 0;
        zero_flag = 0;
        up = 0;
        down = 0;
        instr_in = 32'h00000000;

        // Release reset after some time
        #15 reset = 0;

        // Simulate an interrupt after some time
        #30 irq = 1;
        instr_in = 32'hDEADBEEF; // New instruction to write during interrupt

        // #10 irq = 0; // Clear interrupt
        #10;
        // Simulate normal operation
        #50 up = 1; // Increment PC by 8
        #10 up = 0;  

        #50 down = 1; // Decrement PC by 4
        #10 down = 0;

        #100 $finish; // End simulation
    end

endmodule