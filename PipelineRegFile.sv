module PipelineRegFile (
    input  logic         clk,
    input  logic         reset,
    input  logic  [4:0]  rs1_addr,
    input  logic  [4:0]  rs2_addr,
    input  logic  [4:0]  rd_addr,
    input  logic  [31:0] rd_data,
    input  logic         rd_we,
    output logic [31:0]  rs1_data,
    output logic [31:0]  rs2_data
);

    logic [31:0] regs [31:0];
    // Initialize registers to zero
    // initial begin
    //     integer i;
    //     for (i = 0; i < 32; i = i + 1) begin
    //         regs[i] = 32'b0;
    //     end
    // end
    // Read ports
    assign rs1_data = (rs1_addr == 0) ? 32'b0 : regs[rs1_addr];
    assign rs2_data = (rs2_addr == 0) ? 32'b0 : regs[rs2_addr];

    // Write port
    always_ff @(posedge clk) begin
        if (reset) begin
            integer j;
            for (j = 0; j < 32; j = j + 1) begin
                regs[j] <= 32'b0;
            end
        end else
        if (rd_we && (rd_addr != 0)) begin
            regs[rd_addr] <= rd_data;
        end
    end

endmodule