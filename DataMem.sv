module DataMem (
    input  logic        clk,
    input  logic        we,         // Write enable
    input  logic [31:0] addr,       // 32-bit address
    input  logic [31:0] wdata,      // Write data
    output logic [31:0] rdata      // Read data
);

    // 64 x 32-bit data memory
    logic [31:0] mem [0:63];

    // Read operation (asynchronous)
    assign rdata = mem[addr[31:2]];

    initial begin
        for (int i = 0; i < 64; i++) begin
            mem[i] = 32'b0;
        end
    end

    // Write operation (synchronous)
    always_ff @(posedge clk) begin
        if (we) begin
            mem[addr[31:2]] <= wdata;
        end
    end


endmodule