module RISCV_Pipeline (
    input  logic         clk,
    input  logic         reset,
    input  logic         start,
    input  logic [4:0]   SW,
    output logic [31:0]  pc_out,
    output logic [31:0]  ResultWB
);
    logic [31:0] pc_IF_next, pc_IF, 
                 pc_ID, 
                 pc_EX,
                 
                 pc_plus_4_IF, 
                 pc_plus_4_ID, 
                 pc_plus_4_EX, 
                 pc_plus_4_MEM, 
                 pc_plus_4_WB,
                 
                 pc_target_EX;
    
    logic [31:0] instr_IF, 
                 instr_ID;
    
    logic [6:0]  opcode;
    
    logic [4:0]  rd_ID, rs1_ID, rs2_ID, 
                 rd_EX, rs1_EX, rs2_EX, 
                 rd_MEM, 
                 rd_WB;
    
    logic [31:0] imm_ID, 
                 imm_EX;
    
    logic [31:0] rs1_data_ID, rs2_data_ID, 
                 rs1_data_EX, rs2_data_EX;
    
    logic [31:0] alu_result_EX, 
                 alu_result_MEM,
                 alu_result_WB;
    
    logic        RegWrite_ID, MemWrite_ID, branch_ID, aluSrc_ID, jump_ID,
                 RegWrite_EX, MemWrite_EX, branch_EX, aluSrc_EX, jump_EX, zero_EX,
                 RegWrite_MEM, MemWrite_MEM,
                 RegWrite_WB;

    logic [1:0]  ResultSrc_ID, ImmSrc_ID,
                 ResultSrc_EX, 
                 ResultSrc_MEM,
                 ResultSrc_WB;

    logic [1:0]  aluOp_ID;
    
    logic [3:0]  ALUCtrl_ID, ALUCtrl_EX;

    logic [31:0] SR_A_EX, SR_B_EX, 
                 ReadData_MEM,
                 ReadData_WB; 

    logic [31:0] Write_data_MEM;

    logic [31:0] OperandA, OperandB; 

    logic [2:0]  funct3;
    logic [6:0]  funct7;
                 
                 
    
    // Hazard Unit Signals
    logic        stall_IF, stall_ID, flush_ID, flush_EX;
    logic [1:0]  forwardA_EX, forwardB_EX;

    // IF Stage
    assign pc_plus_4_IF = pc_IF + 32'd4;

    assign pc_IF_next = ((branch_EX & zero_EX) | jump_EX) ? pc_target_EX : pc_plus_4_IF;

    // PC Register
    always_ff @(posedge clk) begin
        if (reset) begin
            pc_IF <= 32'h0;
        end else if (start && !stall_IF) begin
            pc_IF <= pc_IF_next;
        end
        else if (start  && stall_IF) begin
            pc_IF <= pc_IF;
        end

    end
    assign pc_out = pc_IF;

    // Placeholder for Instruction Memory
    IMEM IMEM (
        .pc(pc_IF),
        .clk(clk),
        .reset(reset),
        .write_en(1'b0),
        .write_instr(32'h0),
        .instr_out(instr_IF)
    );

    // IF/ID Pipeline Register
    always_ff @(posedge clk) begin
        if (reset || flush_ID) begin
            pc_ID        <= 32'h0;
            pc_plus_4_ID <= 32'h0;
            instr_ID     <= 32'h0;
        end else if (!stall_ID) begin
            pc_ID        <= pc_IF;
            pc_plus_4_ID <= pc_plus_4_IF;
            instr_ID     <= instr_IF;
        end
        else begin
            pc_ID        <= pc_ID;
            pc_plus_4_ID <= pc_plus_4_ID;
            instr_ID     <= instr_ID;
        end
    end

    // ID Stage
    assign opcode   = instr_ID[6:0];
    assign rd_ID    = instr_ID[11:7];
    assign funct3   = instr_ID[14:12];
    assign rs1_ID   = instr_ID[19:15];
    assign rs2_ID   = instr_ID[24:20];
    assign funct7   = instr_ID[31:25];
     

    // Control Unit
    ControlUnit control_unit (
        .opcode(opcode),
        .regWrite(RegWrite_ID),
        .memWrite(MemWrite_ID),
        .branch(branch_ID),
        .aluOp(aluOp_ID),
        .aluSrc(aluSrc_ID),
        .ImmSrc(ImmSrc_ID),
        .ResultSrc(ResultSrc_ID),
        .jump(jump_ID)
    );

    // ALU Control
    ALUControl alu_control (
        .funct7(funct7),
        .funct3(funct3),
        .ALUOp(aluOp_ID),
        .opcode(opcode),
        .ALUCtrl(ALUCtrl_ID)
    );

    // Sign Extend
    SignExtend sign_extend (
        .instr(instr_ID[31:7]),
        .ImmSrc(ImmSrc_ID),
        .imm_out(imm_ID)
    );

    // Register File
    PipelineRegFile reg_file (
        .clk(clk),
        .reset(reset),
        .rs1_addr(rs1_ID),
        .rs2_addr(rs2_ID),
        .rd_addr(rd_WB),
        .rd_data(ResultWB),
        .rd_we(RegWrite_WB),
        .rs1_data(rs1_data_ID),
        .rs2_data(rs2_data_ID)
    );

    // ID/EX Pipeline Register
    always_ff @(posedge clk) begin
        if (reset || flush_EX) begin
            pc_EX         <= 32'h0;
            pc_plus_4_EX  <= 32'h0;
            rd_EX         <= 5'h0;
            rs1_EX        <= 5'h0;
            rs2_EX        <= 5'h0;
            imm_EX        <= 32'h0;
            rs1_data_EX   <= 32'h0;
            rs2_data_EX   <= 32'h0;
            RegWrite_EX   <= 1'b0;
            MemWrite_EX   <= 1'b0;
            branch_EX     <= 1'b0;
            aluSrc_EX     <= 1'b0;
            jump_EX       <= 1'b0;
            ALUCtrl_EX    <= 4'b0000;
            ResultSrc_EX  <= 2'b00;
        end else begin
            pc_EX         <= pc_ID;
            pc_plus_4_EX  <= pc_plus_4_ID;
            rd_EX         <= rd_ID;
            rs1_EX        <= rs1_ID;
            rs2_EX        <= rs2_ID;
            imm_EX        <= imm_ID;
            rs1_data_EX   <= rs1_data_ID;
            rs2_data_EX   <= rs2_data_ID;
            RegWrite_EX   <= RegWrite_ID;
            MemWrite_EX   <= MemWrite_ID;
            branch_EX     <= branch_ID;
            aluSrc_EX     <= aluSrc_ID;
            jump_EX       <= jump_ID;
            ALUCtrl_EX    <= ALUCtrl_ID;
            ResultSrc_EX  <= ResultSrc_ID;
        end
    end

    // EX Stage
    
    // Branch/Jump Target Calculation
    assign pc_target_EX = pc_EX + imm_EX;

    // Forwarding Muxes
    always_comb begin
        case (forwardA_EX)
            2'b00: SR_A_EX   = rs1_data_EX; // No forwarding
            2'b01: SR_A_EX   = ResultWB;    // Forward from WB stage
            2'b10: SR_A_EX   = alu_result_MEM; // Forward from MEM stage
            default: SR_A_EX = rs1_data_EX;
        endcase

        case (forwardB_EX)
            2'b00: SR_B_EX   = rs2_data_EX; // No forwarding
            2'b01: SR_B_EX   = ResultWB;    // Forward from WB stage
            2'b10: SR_B_EX   = alu_result_MEM; // Forward from MEM stage
            default: SR_B_EX = rs2_data_EX; 
        endcase
    end

    // ALU Operand B Mux
   
    assign OperandA = SR_A_EX;
    assign OperandB = aluSrc_EX ? imm_EX : SR_B_EX;

    // ALU
    ALU alu (
        .a(OperandA),
        .b(OperandB),
        .alu_op(ALUCtrl_EX),
        .result(alu_result_EX),
        .zero(zero_EX)
    );

    // EX/MEM Pipeline Register
    always_ff @(posedge clk) begin
        if (reset) begin
            pc_plus_4_MEM  <= 32'h0;
            rd_MEM         <= 5'h0;
            alu_result_MEM <= 32'h0;
            Write_data_MEM <= 32'h0;
            RegWrite_MEM   <= 1'b0;
            MemWrite_MEM   <= 1'b0;
            ResultSrc_MEM  <= 2'b00;
        end else begin
            pc_plus_4_MEM  <= pc_plus_4_EX;
            rd_MEM         <= rd_EX;
            alu_result_MEM <= alu_result_EX;
            Write_data_MEM <= SR_B_EX; // Use forwarded data
            RegWrite_MEM   <= RegWrite_EX;
            MemWrite_MEM   <= MemWrite_EX;
            ResultSrc_MEM  <= ResultSrc_EX;
        end
    end

    // MEM Stage

    // Data Memory 
    DataMem data_mem (
        .clk(clk),
        .reset(reset),
        .we(MemWrite_MEM),
        .addr(alu_result_MEM),
        .wdata(Write_data_MEM),
        .rdata(ReadData_MEM)
    );

    // MEM/WB Pipeline Register
    always_ff @(posedge clk) begin
        if (reset) begin
            pc_plus_4_WB   <= 32'h0;
            rd_WB          <= 5'h0;
            alu_result_WB  <= 32'h0;
            ReadData_WB    <= 32'h0;
            RegWrite_WB    <= 1'b0;
            ResultSrc_WB   <= 2'b00;
        end else begin
            pc_plus_4_WB   <= pc_plus_4_MEM;
            rd_WB          <= rd_MEM;
            alu_result_WB  <= alu_result_MEM;
            ReadData_WB    <= ReadData_MEM;
            RegWrite_WB    <= RegWrite_MEM;
            ResultSrc_WB   <= ResultSrc_MEM;
        end
    end

    // WB Stage
    always_comb begin
        case (ResultSrc_WB)
            2'b00: ResultWB = alu_result_WB;      // ALU result
            2'b01: ResultWB = ReadData_WB;        // Memory data
            2'b10: ResultWB = pc_plus_4_WB;       // PC + 4 (for JAL/JALR)
            default: ResultWB = alu_result_WB;
        endcase
    end
    

    // Hazard Unit
    HazardUnit hazard_unit (
        .rs1_ID(rs1_ID),
        .rs2_ID(rs2_ID),
        .rd_EX(rd_EX),
        .rs1_EX(rs1_EX),
        .rs2_EX(rs2_EX),
        .PCSrc_EX(branch_EX & zero_EX),
        .ResultSrc_EX(ResultSrc_EX[0]), // Load instruction
        .rd_MEM(rd_MEM),
        .RegWrite_MEM(RegWrite_MEM),
        .rd_WB(rd_WB),
        .RegWrite_WB(RegWrite_WB),
        .stall_IF(stall_IF),
        .stall_ID(stall_ID),
        .flush_ID(flush_ID),
        .flush_EX(flush_EX),
        .forwardA_EX(forwardA_EX),
        .forwardB_EX(forwardB_EX)
    );
endmodule