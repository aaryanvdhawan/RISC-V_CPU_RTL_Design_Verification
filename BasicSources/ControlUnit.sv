module ControlUnit (
    input  logic [6:0] opcode,
    output logic       regWrite,
    output logic       memWrite,
    output logic       branch,
    output logic [1:0] aluOp,
    output logic       aluSrc,
    output logic [1:0] ImmSrc,
    output logic [1:0] ResultSrc, // Added output
    output logic       jump       // Added output for jump
);

    always_comb begin
        // Default values
        regWrite  = 0;
        memWrite  = 0;
        branch    = 0;
        aluOp     = 2'b00;
        aluSrc    = 0;
        ImmSrc    = 2'b00;
        ResultSrc = 2'b00; // Default: ALU result
        jump      = 0;

        case (opcode)
            7'b0110011: begin // R-type
                regWrite  = 1;
                aluOp     = 2'b10;
                aluSrc    = 0;
                ImmSrc    = 2'b00;
                ResultSrc = 2'b00; // ALU result
                jump      = 0;
            end
            7'b0000011: begin // Load (e.g., LW)
                regWrite  = 1;
                aluOp     = 2'b00;
                aluSrc    = 1;
                ImmSrc    = 2'b00;
                ResultSrc = 2'b01; // Memory data
                jump      = 0;
            end
            7'b0100011: begin // Store (e.g., SW)
                memWrite  = 1;
                aluOp     = 2'b00;
                aluSrc    = 1;
                ImmSrc    = 2'b01;
                ResultSrc = 2'b00; // Not used
                jump      = 0;
            end
            7'b1100011: begin // Branch (e.g., BEQ)
                branch    = 1;
                aluOp     = 2'b01;
                aluSrc    = 0;
                ImmSrc    = 2'b10;
                ResultSrc = 2'b00; // Not used
                jump      = 0;
            end
            7'b0010011: begin // I-type (e.g., ADDI)
                regWrite  = 1;
                aluOp     = 2'b10;
                aluSrc    = 1;
                ImmSrc    = 2'b00;
                ResultSrc = 2'b00; // ALU result
                jump      = 0;
            end
            7'b1101111: begin // JAL (Jump and Link)
                regWrite  = 1;
                aluOp     = 2'b00;
                aluSrc    = 0;
                ImmSrc    = 2'b11;
                ResultSrc = 2'b10; // PC+4 or jump address
                jump      = 1;
            end
            7'b1100111: begin // JALR (Jump and Link Register)
                regWrite  = 1;
                aluOp     = 2'b00;
                aluSrc    = 1;
                ImmSrc    = 2'b00;
                ResultSrc = 2'b10; // PC+4 or jump address
                jump      = 1;
            end
            default: begin
                // Keep defaults
            end
        endcase
    end

endmodule