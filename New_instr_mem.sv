module IMEM #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = 32
)(
    input logic [ADDR_WIDTH-1:0] pc,
    input logic clk,
    input logic reset,
    input logic  [DATA_WIDTH-1:0] instr_in,
    input logic                  write_enable,
    output logic [DATA_WIDTH-1:0] instr_out
);

    logic [DATA_WIDTH-1:0] mem [0:(1<<ADDR_WIDTH)-1];

    initial begin
        integer i;
        // Initialize all memory locations to zero
        for (i = 0; i < (1<<ADDR_WIDTH); i = i + 1) begin
            mem[i] = 'h0;
        end
        // Load memory contents from file (overwrites zeros where file has data)
        $readmemh("program.mem", mem);
    end

    always_ff @(posedge clk) begin
        if (reset) begin
            instr_out <= 'h0;
        end else if (write_enable) begin
            mem[pc[11:2]] <= instr_in;
        end
    end

    assign instr_out = write_enable ? '0 : mem[pc[11:2]];

endmodule