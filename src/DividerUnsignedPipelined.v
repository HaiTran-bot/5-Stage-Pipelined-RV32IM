`timescale 1ns / 1ps

module DividerUnsignedPipelined (
    input             clk, 
    input             rst,
    input             stall,
    input      [31:0] i_dividend,
    input      [31:0] i_divisor,
    output     [31:0] o_remainder,
    output     [31:0] o_quotient
);

    reg [31:0] stage_dividend [0:7];
    reg [31:0] stage_remainder[0:7];
    reg [31:0] stage_quotient [0:7];
    reg [31:0] stage_divisor  [0:7];

    always @(*) begin
        stage_dividend[0]  = i_dividend;
        stage_divisor[0]   = i_divisor;
        stage_remainder[0] = 32'b0;
        stage_quotient[0]  = 32'b0;
    end

    genvar i, j;
    generate
        for (i = 0; i < 7; i = i + 1) begin : STAGE
            
            wire [31:0] t_dividend [0:4];
            wire [31:0] t_remainder[0:4];
            wire [31:0] t_quotient [0:4];

            assign t_dividend[0]  = stage_dividend[i];
            assign t_remainder[0] = stage_remainder[i];
            assign t_quotient[0]  = stage_quotient[i];

            for (j = 0; j < 4; j = j + 1) begin : ITER
                divu_1iter u_iter (
                    .i_dividend (t_dividend[j]),
                    .i_divisor  (stage_divisor[i]),
                    .i_remainder(t_remainder[j]),
                    .i_quotient (t_quotient[j]),
                    .o_dividend (t_dividend[j+1]),
                    .o_remainder(t_remainder[j+1]),
                    .o_quotient (t_quotient[j+1])
                );
            end

            always @(posedge clk) begin
                if (rst) begin
                    stage_dividend[i+1]  <= 0;
                    stage_remainder[i+1] <= 0;
                    stage_quotient[i+1]  <= 0;
                    stage_divisor[i+1]   <= 0;
                end else begin
                    stage_dividend[i+1]  <= t_dividend[4];
                    stage_remainder[i+1] <= t_remainder[4];
                    stage_quotient[i+1]  <= t_quotient[4];
                    stage_divisor[i+1]   <= stage_divisor[i];
                end
            end
        end
    endgenerate

    wire [31:0] f_dividend [0:4];
    wire [31:0] f_remainder[0:4];
    wire [31:0] f_quotient [0:4];
    
    assign f_dividend[0]  = stage_dividend[7];
    assign f_remainder[0] = stage_remainder[7];
    assign f_quotient[0]  = stage_quotient[7];

    generate
        for (j = 0; j < 4; j = j + 1) begin : FINAL_ITER
            divu_1iter u_final (
                .i_dividend (f_dividend[j]),
                .i_divisor  (stage_divisor[7]),
                .i_remainder(f_remainder[j]),
                .i_quotient (f_quotient[j]),
                .o_dividend (f_dividend[j+1]),
                .o_remainder(f_remainder[j+1]),
                .o_quotient (f_quotient[j+1])
            );
        end
    endgenerate

    assign o_quotient  = f_quotient[4];
    assign o_remainder = f_remainder[4];

endmodule

module divu_1iter (
   input   [31:0] i_dividend,
   input   [31:0] i_divisor,
   input   [31:0] i_remainder,
   input   [31:0] i_quotient,
   output reg [31:0] o_dividend,
   output reg [31:0] o_remainder,
   output reg [31:0] o_quotient       
);
   wire [32:0] remainder_next;
   wire [32:0] diff;
   wire condition;

   assign remainder_next = ({1'b0, i_remainder} << 1) | {32'd0, (i_dividend >> 31) & 1};
   assign diff = remainder_next - {1'b0, i_divisor};
   assign condition = (remainder_next >= {1'b0, i_divisor});

   always @(*) begin
    o_remainder = condition ? diff[31:0] : remainder_next[31:0];
    o_quotient  = (i_quotient << 1) | {31'b0, condition};
    o_dividend = i_dividend << 1;
   end
endmodule







