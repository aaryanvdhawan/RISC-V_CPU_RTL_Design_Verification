module ALU #(
    parameter WIDTH = 32
) (
    input  logic [WIDTH-1:0]  a,
    input  logic [WIDTH-1:0]  b,
    input  logic [3:0]        alu_op, // ALU operation selector
    output logic [WIDTH-1:0]  result,
    output logic              zero
);

    // ALU operation encoding (example for RISC-V)
    localparam ALU_ADD  = 4'b0000;
    localparam ALU_SUB  = 4'b0001;
    localparam ALU_AND  = 4'b0010;
    localparam ALU_OR   = 4'b0011;
    localparam ALU_XOR  = 4'b0100;
    localparam ALU_SLL  = 4'b0101;
    localparam ALU_SRL  = 4'b0110;
    localparam ALU_SRA  = 4'b0111;
    localparam ALU_SLT  = 4'b1000;
    localparam ALU_SLTU = 4'b1001;

    always_comb begin
        case (alu_op)
            ALU_ADD:   result = a + b;
            ALU_SUB:   result = a - b;
            ALU_AND:   result = a & b;
            ALU_OR:    result = a | b;
            ALU_XOR:   result = a ^ b;
            ALU_SLL:   result = a << b[4:0];
            ALU_SRL:   result = a >> b[4:0];
            ALU_SRA:   result = $signed(a) >>> b[4:0];
            ALU_SLT:   result = ($signed(a) < $signed(b)) ? 1 : 0;
            ALU_SLTU:  result = (a < b) ? 1 : 0;
            default:   result = '0;
        endcase
    end

    assign zero = (result == 0);

endmodule