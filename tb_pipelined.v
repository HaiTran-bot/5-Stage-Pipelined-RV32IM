`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 12/05/2025 01:21:03 AM
// Design Name: 
// Module Name: tb_pipelined
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
module tb_pipelined;

    // Inputs
    reg clk;
    reg rst;

    // Outputs
    wire halt;
    wire [31:0] trace_pc;
    wire [31:0] trace_inst;

    Processor uut (
        .clk(clk),
        .rst(rst),
        .halt(halt),
        .trace_writeback_pc(trace_pc),
        .trace_writeback_inst(trace_inst)
    );

    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    initial begin
        // Reset hệ thống
        rst = 1;
        #50;
        rst = 0;
        
        $display("=== START SIMULATION (5-Stage Pipeline) ===");
        $display("Time\t\tWB_PC\t\tInstruction\tResult(Writeback)");
        
        #50000;
        $display("TIMEOUT: Simulation ran too long without HALT.");
        $finish;
    end

    always @(posedge halt) begin
        $display("=== HALT DETECTED ===");
        $display("Test PASSED at time %t", $time);
        #20;
        $finish;
    end

    always @(negedge clk) begin
        if (!rst && trace_pc != 0) begin
            $display("%0t\t%h\t%h\tReg[x%0d] <= %h", 
                     $time, 
                     trace_pc, 
                     trace_inst,
                     uut.datapath.w_rd,
                     uut.datapath.w_wb_data
            );
        end
    end

endmodule
