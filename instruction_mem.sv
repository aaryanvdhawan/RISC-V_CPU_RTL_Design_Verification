module instruction_mem  (
    input  logic [31:0]            pc,         // Address from PC
    input  logic                   clk,        // Clock signal
    input  logic                   reset,      // Reset signal
    output logic [31:0]            instr_out   // Instruction at PC
);

    logic [31:0] mem [0:1023]; // 1K x 32-bit instruction memory
    

    initial begin
        $readmemh("program.mem", mem);
    end

    always_ff @(posedge clk) begin
        if (reset)
            instr_out <= 32'b0;
        else
            instr_out <= mem[pc[11:2]];
    end
    
endmodule