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
   assign pout = &pin;
  
   assign gout = gin[3] | (pin[3] & gin[2]) | ((&pin[3:2]) & gin[1]) | ((&pin[3:1]) & gin[0]);
   // c1 = g0 | (p0 & cin)
   assign cout[0] = gin[0] | (pin[0] & cin);
   // c2 = g1 | (p1 & g0) | (p1&p0 & cin)
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | ((&pin[1:0]) & cin);
   // c3 = g2 | (p2 & g1) | (p2&p1 & g0) | (p2&p1&p0 & cin)
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | ((&pin[2:1]) & gin[0]) | ((&pin[2:0]) & cin);
endmodule
/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);
   // TODO: your code here
     assign pout = &pin; // p7 & ... & p0
   assign gout = gin[7]
               | (pin[7] & gin[6])
               | ((&pin[7:6]) & gin[5])
               | ((&pin[7:5]) & gin[4])
               | ((&pin[7:4]) & gin[3])
               | ((&pin[7:3]) & gin[2])
               | ((&pin[7:2]) & gin[1])
               | ((&pin[7:1]) & gin[0]);
   // c1
   assign cout[0] = gin[0] | (pin[0] & cin);
   // c2
   assign cout[1] = gin[1]
                  | (pin[1] & gin[0])
                  | ((&pin[1:0]) & cin);
   // c3
   assign cout[2] = gin[2]
                  | (pin[2] & gin[1])
                  | ((&pin[2:1]) & gin[0])
                  | ((&pin[2:0]) & cin);
   // c4
   assign cout[3] = gin[3]
                  | (pin[3] & gin[2])
                  | ((&pin[3:2]) & gin[1])
                  | ((&pin[3:1]) & gin[0])
                  | ((&pin[3:0]) & cin);
   // c5
   assign cout[4] = gin[4]
                  | (pin[4] & gin[3])
                  | ((&pin[4:3]) & gin[2])
                  | ((&pin[4:2]) & gin[1])
                  | ((&pin[4:1]) & gin[0])
                  | ((&pin[4:0]) & cin);
   // c6
   assign cout[5] = gin[5]
                  | (pin[5] & gin[4])
                  | ((&pin[5:4]) & gin[3])
                  | ((&pin[5:3]) & gin[2])
                  | ((&pin[5:2]) & gin[1])
                  | ((&pin[5:1]) & gin[0])
                  | ((&pin[5:0]) & cin);
   // c7
   assign cout[6] = gin[6]
                  | (pin[6] & gin[5])
                  | ((&pin[6:5]) & gin[4])
                  | ((&pin[6:4]) & gin[3])
                  | ((&pin[6:3]) & gin[2])
                  | ((&pin[6:2]) & gin[1])
                  | ((&pin[6:1]) & gin[0])
                  | ((&pin[6:0]) & cin);
endmodule
module cla
  (input wire [31:0] a, b,
   input wire cin,
   output wire [31:0] sum);
   // TODO: your code here
   //gp1
   wire [31:0] g, p;
   assign g = a & b;
   assign p = a | b;
   //block0 = bits [7:0], block1 = [15:8], block2 = [23:16], block3 = [31:24]
   wire gout0, pout0;
   wire gout1, pout1;
   wire gout2, pout2;
   wire gout3, pout3;
   wire [6:0] cout8_0;
   wire [6:0] cout8_1;
   wire [6:0] cout8_2;
   wire [6:0] cout8_3;
   wire c_block0, c_block1, c_block2, c_block3;
   assign c_block0 = cin;
   // instantiate gp8
   gp8 gp8_0(.gin(g[7:0]), .pin(p[7:0]), .cin(c_block0), .gout(gout0), .pout(pout0), .cout(cout8_0));
   // c_block1 depends on gout0/pout0 and c_block0
   assign c_block1 = gout0 | (pout0 & c_block0);
   gp8 gp8_1(.gin(g[15:8]), .pin(p[15:8]), .cin(c_block1), .gout(gout1), .pout(pout1), .cout(cout8_1));
   assign c_block2 = gout1 | (pout1 & c_block1);
   gp8 gp8_2(.gin(g[23:16]), .pin(p[23:16]), .cin(c_block2), .gout(gout2), .pout(pout2), .cout(cout8_2));
   assign c_block3 = gout2 | (pout2 & c_block2);
   gp8 gp8_3(.gin(g[31:24]), .pin(p[31:24]), .cin(c_block3), .gout(gout3), .pout(pout3), .cout(cout8_3));
   wire [31:0] carry;
   assign carry[0] = c_block0;
   assign carry[1] = cout8_0[0];
   assign carry[2] = cout8_0[1];
   assign carry[3] = cout8_0[2];
   assign carry[4] = cout8_0[3];
   assign carry[5] = cout8_0[4];
   assign carry[6] = cout8_0[5];
   assign carry[7] = cout8_0[6];
   assign carry[8] = c_block1;
   assign carry[9] = cout8_1[0];
   assign carry[10] = cout8_1[1];
   assign carry[11] = cout8_1[2];
   assign carry[12] = cout8_1[3];
   assign carry[13] = cout8_1[4];
   assign carry[14] = cout8_1[5];
   assign carry[15] = cout8_1[6];
   assign carry[16] = c_block2;
   assign carry[17] = cout8_2[0];
   assign carry[18] = cout8_2[1];
   assign carry[19] = cout8_2[2];
   assign carry[20] = cout8_2[3];
   assign carry[21] = cout8_2[4];
   assign carry[22] = cout8_2[5];
   assign carry[23] = cout8_2[6];
   assign carry[24] = c_block3;
   assign carry[25] = cout8_3[0];
   assign carry[26] = cout8_3[1];
   assign carry[27] = cout8_3[2];
   assign carry[28] = cout8_3[3];
   assign carry[29] = cout8_3[4];
   assign carry[30] = cout8_3[5];
   assign carry[31] = cout8_3[6];
   // final sum bit: sum[i] = a[i] ^ b[i] ^ carry[i]
   assign sum = a ^ b ^ carry;
endmodule
