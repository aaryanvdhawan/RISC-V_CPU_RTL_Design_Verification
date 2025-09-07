module ALUControl (
    input  logic [6:0] funct7,
    input  logic [2:0] funct3,
    input  logic [1:0] ALUOp,
    input  logic [6:0] opcode,
    output logic [3:0] ALUCtrl
);

    always_comb begin
        unique case (ALUOp)
            2'b00: ALUCtrl = 4'b0010; // Load/Store: ADD
            2'b01: ALUCtrl = 4'b0110; // Branch: SUB
            2'b10: begin // R-type/I-type
                unique case (opcode)
                    7'b0110011: begin // R-type
                        unique case ({funct7, funct3})
                            {7'b0000000, 3'b000}: ALUCtrl = 4'b0010; // ADD
                            {7'b0100000, 3'b000}: ALUCtrl = 4'b0110; // SUB
                            {7'b0000000, 3'b111}: ALUCtrl = 4'b0000; // AND
                            {7'b0000000, 3'b110}: ALUCtrl = 4'b0001; // OR
                            {7'b0000000, 3'b100}: ALUCtrl = 4'b0011; // XOR
                            {7'b0000000, 3'b001}: ALUCtrl = 4'b0100; // SLL
                            {7'b0000000, 3'b101}: ALUCtrl = 4'b0101; // SRL
                            {7'b0100000, 3'b101}: ALUCtrl = 4'b0111; // SRA
                            {7'b0000000, 3'b010}: ALUCtrl = 4'b1000; // SLT
                            {7'b0000000, 3'b011}: ALUCtrl = 4'b1001; // SLTU
                            default: ALUCtrl = 4'b1111;
                        endcase
                    end
                    7'b0010011: begin // I-type
                        unique case (funct3)
                            3'b000: ALUCtrl = 4'b0010; // ADDI
                            3'b111: ALUCtrl = 4'b0000; // ANDI
                            3'b110: ALUCtrl = 4'b0001; // ORI
                            3'b100: ALUCtrl = 4'b0011; // XORI
                            3'b001: ALUCtrl = 4'b0100; // SLLI
                            3'b101: begin
                                if (funct7 == 7'b0000000)
                                    ALUCtrl = 4'b0101; // SRLI
                                else if (funct7 == 7'b0100000)
                                    ALUCtrl = 4'b0111; // SRAI
                                else
                                    ALUCtrl = 4'b1111;
                            end
                            3'b010: ALUCtrl = 4'b1000; // SLTI
                            3'b011: ALUCtrl = 4'b1001; // SLTIU
                            default: ALUCtrl = 4'b1111;
                        endcase
                    end
                    default: ALUCtrl = 4'b1111;
                endcase
            end
            default: ALUCtrl = 4'b1111;
        endcase
    end

endmodule