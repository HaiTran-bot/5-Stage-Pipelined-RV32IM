`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company:
// Engineer:
//
// Create Date: 10/29/2025 07:40:47 AM
// Design Name:
// Module Name: cla
// Project Name:
// Target Devices:
// Tool Versions:
// Description:
//
// Dependencies:
//
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////
/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule
/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);
   
   // TODO: your code here
    wire [3:0] g_internal, p_internal;
           
    gp1 u0(.a(gin[0]), .b(pin[0]), .g(g_internal[0]), .p(p_internal[0]));
    gp1 u1(.a(gin[1]), .b(pin[1]), .g(g_internal[1]), .p(p_internal[1]));
    gp1 u2(.a(gin[2]), .b(pin[2]), .g(g_internal[2]), .p(p_internal[2]));
    gp1 u3(.a(gin[3]), .b(pin[3]), .g(g_internal[3]), .p(p_internal[3]));

    assign pout = &p_internal;
  
    assign gout = g_internal[3] 
                | (p_internal[3] & g_internal[2]) 
                | ((&p_internal[3:2]) & g_internal[1]) 
                | ((&p_internal[3:1]) & g_internal[0]);

    // c1
    assign cout[0] = g_internal[0] | (p_internal[0] & cin);
    // c2
    assign cout[1] = g_internal[1] | (p_internal[1] & g_internal[0]) | ((&p_internal[1:0]) & cin);
    // c3
    assign cout[2] = g_internal[2] | (p_internal[2] & g_internal[1]) | ((&p_internal[2:1]) & g_internal[0]) | ((&p_internal[2:0]) & cin);
endmodule
/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);
   // TODO: your code here
    wire gout_low, pout_low;   
    wire gout_high, pout_high;
    wire c_mid;                
    wire [2:0] cout_low;     
    wire [2:0] cout_high;

    gp4 gp4_low (
        .gin(gin[3:0]), 
        .pin(pin[3:0]),
        .cin(cin),
        .gout(gout_low), 
        .pout(pout_low), 
        .cout(cout_low)
    );

    assign c_mid = gout_low | (pout_low & cin);

    gp4 gp4_high (
        .gin(gin[7:4]), 
        .pin(pin[7:4]),
        .cin(c_mid),
        .gout(gout_high), 
        .pout(pout_high), 
        .cout(cout_high)
    );

    assign pout = pout_high & pout_low;
    assign gout = gout_high | (pout_high & gout_low);

    // cout [6:0] = {c7, c6, c5, c4, c3, c2, c1}
    assign cout = {cout_high, c_mid, cout_low};
endmodule
module cla
  (input wire [31:0] a, b,
   input wire cin,
   output wire [31:0] sum);
   // TODO: your code here
    wire [3:0] G_blk, P_blk; 
    wire [3:0] C_blk;        
    wire [6:0] cout8_0, cout8_1, cout8_2, cout8_3;

    assign C_blk[0] = cin;

    // Block 0: Bits 7:0
    // LƯU Ý: Truyền a vào gin, b vào pin
    gp8 gp8_0(.gin(a[7:0]), .pin(b[7:0]), .cin(C_blk[0]), 
              .gout(G_blk[0]), .pout(P_blk[0]), .cout(cout8_0));

    // Block 1: Bits 15:8
    assign C_blk[1] = G_blk[0] | (P_blk[0] & C_blk[0]);
    gp8 gp8_1(.gin(a[15:8]), .pin(b[15:8]), .cin(C_blk[1]), 
              .gout(G_blk[1]), .pout(P_blk[1]), .cout(cout8_1));

    // Block 2: Bits 23:16
    assign C_blk[2] = G_blk[1] | (P_blk[1] & C_blk[1]);
    gp8 gp8_2(.gin(a[23:16]), .pin(b[23:16]), .cin(C_blk[2]), 
              .gout(G_blk[2]), .pout(P_blk[2]), .cout(cout8_2));

    // Block 3: Bits 31:24
    assign C_blk[3] = G_blk[2] | (P_blk[2] & C_blk[2]);
    gp8 gp8_3(.gin(a[31:24]), .pin(b[31:24]), .cin(C_blk[3]), 
              .gout(G_blk[3]), .pout(P_blk[3]), .cout(cout8_3));
           
    wire [31:0] carry;
    assign carry[7:0]   = {cout8_0, C_blk[0]};
    assign carry[15:8]  = {cout8_1, C_blk[1]};
    assign carry[23:16] = {cout8_2, C_blk[2]};
    assign carry[31:24] = {cout8_3, C_blk[3]};

    assign sum = a ^ b ^ carry;
endmodule
