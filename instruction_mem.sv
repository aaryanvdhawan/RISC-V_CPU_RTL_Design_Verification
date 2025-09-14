module instruction_mem  (
    input  logic [31:0]            pc,         // Address from PC
    input  logic                   clk,        // Clock signal
    input  logic [31:0]            write_instr,
    input  logic                   write_en,
    output logic [31:0]            instr_out   // Instruction at PC
);
    // 64 x 32-bit instruction memory
    logic [31:0] mem [0:63]; 
    
    initial begin
        for (int i = 0; i < 64; i++) begin
            mem[i] = 32'b0;
        end
        $readmemh("program.mem", mem);
    end

    // Asynchronous read
    assign instr_out = mem[pc[31:2]]; // Word-aligned access

    // Synchronous write
    always_ff @(posedge clk) begin
        if (write_en) begin
            mem[pc[31:2]] <= write_instr;
        end
    end

endmodule