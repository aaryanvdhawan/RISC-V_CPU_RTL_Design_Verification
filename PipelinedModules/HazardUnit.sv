module HazardUnit (
    
    input  logic [4:0]  rs1_ID,
    input  logic [4:0]  rs2_ID,
    input  logic [4:0]  rd_EX,
    input  logic [4:0]  rs1_EX,
    input  logic [4:0]  rs2_EX,
    input  logic        PCSrc_EX,
    input  logic        ResultSrc_EX,
    input  logic [4:0]  rd_MEM,
    input  logic        RegWrite_MEM,
    input  logic [4:0]  rd_WB,
    input  logic        RegWrite_WB,

    output logic        stall_IF,
    output logic        stall_ID,
    output logic        flush_ID,
    output logic        flush_EX,
    output logic [1:0]  forwardA_EX,
    output logic [1:0]  forwardB_EX
);

    // Load-use hazard detection
    logic load_use_hazard;
    assign load_use_hazard = ResultSrc_EX && ((rs1_ID == rd_EX) || (rs2_ID == rd_EX));

    // Control hazard detection
    logic control_hazard;
    assign control_hazard = PCSrc_EX || ResultSrc_EX;

    // Stall and flush signals
    assign stall_IF = load_use_hazard;
    assign stall_ID = load_use_hazard;
    assign flush_ID = PCSrc_EX;
    assign flush_EX = load_use_hazard || control_hazard;

    // Forwarding logic for EX stage
    always_comb begin
        if(rs1_EX == rd_MEM && RegWrite_MEM && (rs1_EX != 0)) begin
            forwardA_EX = 2'b10;
        end else if(rs1_EX == rd_WB && RegWrite_WB && (rs1_EX != 0)) begin
            forwardA_EX = 2'b01; // Forward from WB stage
        end else begin
            forwardA_EX = 2'b00; // No forwarding
        end
    end

    always_comb begin
        if(rs2_EX == rd_MEM && RegWrite_MEM && (rs2_EX != 0)) begin
            forwardB_EX = 2'b10;
        end else if(rs2_EX == rd_WB && RegWrite_WB && (rs2_EX != 0)) begin
            forwardB_EX = 2'b01; // Forward from WB stage
        end else begin
            forwardB_EX = 2'b00; // No forwarding
        end
    end

endmodule
