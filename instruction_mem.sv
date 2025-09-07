module instruction_mem #(
    parameter ADDR_WIDTH = 10, // 1024 locations
    parameter DATA_WIDTH = 32
) (
    input  logic                   clk,        // Clock
    input  logic                   rst,        // Reset
    input  logic [ADDR_WIDTH-1:0]  pc,         // Address from PC
    output logic [DATA_WIDTH-1:0]  instr_out   // Instruction at PC
);

    // 1KB instruction memory (1024 x 32-bit words)
    logic [DATA_WIDTH-1:0] mem [0:(1<<ADDR_WIDTH)-1];

    // Synchronous read
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            instr_out <= '0;
        else
            instr_out <= mem[pc];
    end

    // Initialize memory (optionally from file)
    initial begin
        // Optionally load from file:
        // $readmemh("instructions.hex", mem);
        // Or zero out memory:
        for (int i = 0; i < (1<<ADDR_WIDTH); i++) begin
            mem[i] = 32'b0;
        end
    end

endmodule