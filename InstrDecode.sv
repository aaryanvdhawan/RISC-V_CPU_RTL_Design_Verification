module InstrDecode (
    input  logic [31:0] instr,
    output logic [6:0]  opcode,
    output logic [4:0]  rs1,
    output logic [4:0]  rs2,
    output logic [4:0]  rd,
    output logic [6:0]  funct7,
    output logic [2:0]  funct3,
    output logic [31:0] imm_I,
    output logic [31:0] imm_S,
    output logic [31:0] imm_B,
    output logic [31:0] imm_U,
    output logic [31:0] imm_J
);

    // R-type fields
    assign opcode = instr[6:0];
    assign rd     = instr[11:7];
    assign funct3 = instr[14:12];
    assign rs1    = instr[19:15];
    assign rs2    = instr[24:20];
    assign funct7 = instr[31:25];

    assign imm_I = {funct7, rs2};
    assign 

    

endmodule