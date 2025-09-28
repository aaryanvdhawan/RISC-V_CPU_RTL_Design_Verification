module SignExtend #(
    parameter OUT_WIDTH = 32      // Output width (e.g., 32 bits)
) (
    input  logic [31:7]      instr,   // Instruction bits [31:7]
    input  logic [1:0]       ImmSrc,  // 2-bit immediate source selector
    output logic [OUT_WIDTH-1:0] imm_out
);

    logic [11:0] imm_I, imm_S;
    logic [12:0] imm_B;
    logic [20:0] imm_J;

    // I-type immediate: instr[31:20]
    assign imm_I = instr[31:20];

    // S-type immediate: instr[31:25] (7 bits), instr[11:7] (5 bits)
    assign imm_S = {instr[31:25], instr[11:7]};

    // B-type immediate: instr[31], instr[7], instr[30:25], instr[11:8], 0
    assign imm_B = {instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};

    // J-type immediate: instr[31], instr[19:12], instr[20], instr[30:21], 0
    assign imm_J = {instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};

    always_comb begin
        case (ImmSrc)
            2'b00: imm_out = {{(OUT_WIDTH-12){imm_I[11]}}, imm_I};      // I-type
            2'b01: imm_out = {{(OUT_WIDTH-12){imm_S[11]}}, imm_S};      // S-type
            2'b10: imm_out = {{(OUT_WIDTH-13){imm_B[12]}}, imm_B};      // B-type (13 bits)
            2'b11: imm_out = {{(OUT_WIDTH-21){imm_J[20]}}, imm_J};      // J-type (21 bits)
            default: imm_out = '0;
        endcase
    end

endmodule