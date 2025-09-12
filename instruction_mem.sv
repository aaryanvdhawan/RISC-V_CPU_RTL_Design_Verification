module instruction_mem  (
    input  logic [31:0]            pc,         // Address from PC
    input  logic                   clk,        // Clock signal
    input  logic                   reset,      // Reset signal
    input  logic                   start,         // Start signal to begin execution
    output logic [31:0]            instr_out   // Instruction at PC
);

    logic [31:0] mem [0:1023]; // 1K x 32-bit instruction memory
    localparam ADDR_WIDTH = 10; // 2^10 = 1024 locations

    initial begin
        integer i;
        // Initialize all memory locations to zero
        for (i = 0; i < (1<<ADDR_WIDTH); i = i + 1) begin
            mem[i] = 'h0;
        end
        $readmemh("program.mem", mem);
    end

    always_ff @(posedge clk) begin
        if (reset)
            instr_out <= 32'b0;
        else if (start)
            instr_out <= mem[pc[11:2]]; // Fetch instruction based on PC
        else
            instr_out <= '0; // Hold the instruction if start is not high
    end
    
endmodule