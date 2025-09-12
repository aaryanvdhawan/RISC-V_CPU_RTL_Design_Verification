module RISCV_Top (
    input  logic         clk,
    input  logic         reset,
    input  logic         start,
    output logic [31:0]  write_back_data
);

    // Wires for inter-module connections
    logic        regWrite, memWrite, branch, aluSrc, jump;
    logic [1:0]  aluOp, ImmSrc, ResultSrc;
    logic [3:0]  alu_ctrl;
    logic [31:0] instr, pc, pc_next, pc_plus_4, pc_target;
    logic [31:0] imm, rs1_data, rs2_data, alu_result, read_data;
    logic        zero_flag;

    // Program Counter
    assign pc_plus_4 = pc + 32'd4;

    always_comb begin
        if (jump)
            pc_next = pc_target;
        else if (branch & zero_flag)
            pc_next = pc_target;
        else
            pc_next = pc_plus_4;
    end

    // Instantiate Program Counter
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            pc <= 32'h0;
        else if(start)
            pc <= pc_next;
        else
            pc <= pc; // Hold the PC value if start is not high
    end

    // assign pc_out = pc;

    // Instruction Memory
    instruction_mem imem (
        .pc(pc),
        .clk(clk),
        .reset(reset),
        .start(start),
        .instr_out(instr)
    );
    // assign instr_out = instr;

    // Instruction Decode
    logic [6:0] opcode;
    logic [4:0] rs1, rs2, rd;
    logic [2:0] funct3;
    logic [6:0] funct7;

    assign opcode = instr[6:0];
    assign rd = instr[11:7];
    assign funct3 = instr[14:12];
    assign rs1 = instr[19:15];
    assign rs2 = instr[24:20];
    assign funct7 = instr[31:25];

    // Control Unit
    ControlUnit ctrl (
        .opcode(opcode),
        .regWrite(regWrite),
        .memWrite(memWrite),
        .branch(branch),
        .aluOp(aluOp),
        .aluSrc(aluSrc),
        .ImmSrc(ImmSrc),
        .ResultSrc(ResultSrc),
        .jump(jump)
    );

    // Sign Extend
    SignExtend imm_gen (
        .instr(instr[31:7]),
        .ImmSrc(ImmSrc),
        .imm_out(imm)
    );

    // Register File
    RegFile reg_file (
        .clk(clk),
        .rs1_addr(rs1),
        .rs2_addr(rs2),
        .rd_addr(rd),
        .rd_data(write_back_data),
        .rd_we(regWrite),
        .rs1_data(rs1_data),
        .rs2_data(rs2_data)
    );

    // ALU Control
    ALUControl alu_control (
        .funct7(funct7),
        .funct3(funct3),
        .ALUOp(aluOp),
        .opcode(opcode),
        .ALUCtrl(alu_ctrl)
    );

    // ALU
    logic [31:0] alu_in_2;
    assign alu_in_2 = aluSrc ? imm : rs2_data;

    ALU alu (
        .a(rs1_data),
        .b(alu_in_2),
        .alu_op(alu_ctrl),
        .result(alu_result),
        .zero(zero_flag)
    );
    // assign alu_result_out = alu_result;

    assign pc_target = pc + imm;

    // Data Memory
    DataMem data_mem (
        .clk(clk),
        .rst(reset),
        .we(memWrite),
        .addr(alu_result),
        .wdata(rs2_data),
        .rdata(read_data)
    );
    // assign mem_write_out = memWrite;
    // assign write_data_out = rs2_data;


    // Write Back Mux
    always_comb begin
        case (ResultSrc)
            2'b00:   write_back_data = alu_result;
            2'b01:   write_back_data = read_data;
            2'b10:   write_back_data = pc_plus_4;
            default: write_back_data = alu_result;
        endcase
    end

endmodule