module PC_Counter_IRQ(
    input logic clk,
    input logic reset,
    input logic irq,
    input logic jump,
    input logic [31:0] pc_target,
    input logic branch,
    input logic zero_flag,
    input logic up,
    input logic down,
    output logic [31:0] pc
);

    logic [31:0] pc_next;
    logic [31:0] pc_plus_4;

    

    always_comb begin
        unique if (jump)
            pc_next = pc_target;
        else if (branch & zero_flag)
            pc_next = pc_target;
        else begin
            if (up)
                pc_next = pc + 4; // Increment PC by 4
            else if (down)
                pc_next = pc - 4; // Decrement PC by 4 if down signal is high
            else
                pc_next = pc + 4; // Normal increment by 4 if neither up nor down is high
        end
            
    end

    // Instantiate Program Counter
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            pc <= 32'h0;
        else if (irq) // pause the PC when an interrupt is high
            if(up || down)
                pc <= pc_next; // Allow PC to update if up or down is high during interrupt
            else
                pc <= pc; // Hold the PC value during interrupt if neither up nor down is high
        else
            pc <= pc_next;
    end

endmodule
