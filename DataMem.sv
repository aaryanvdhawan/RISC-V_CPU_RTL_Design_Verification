module DataMem (
    input  logic        clk,
    input  logic        rst,        // Active-high synchronous reset
    input  logic        we,         // Write enable
    input  logic [31:0] addr,       // 32-bit address
    input  logic [31:0] wdata,      // Write data
    output logic [31:0] rdata,      // Read data
    input  logic [9:0]  sw,         // Switch input for FPGA display bypass
    output logic [31:0] hex_led_data // Output to hex/LEDs
);

    // 4KB memory (1024 x 32-bit words)
    logic [31:0] mem [0:1023];

    // Read operation (asynchronous)
    assign rdata = mem[addr[11:2]];

    initial begin
        for (int i = 0; i < 1024; i++) begin
            mem[i] = 32'b0;
        end
    end

    // Write operation (synchronous), with synchronous reset
    always_ff @(posedge clk) begin
        if (rst) begin
            for (int i = 0; i < 1024; i++) begin
                mem[i] <= 32'b0;
            end
        end else if (we) begin
            mem[addr[11:2]] <= wdata;
        end
    end

    // FPGA display bypass
    // Expose selected memory location to hex/LEDs
    assign hex_led_data = mem[sw];

endmodule