`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31

// inst. are 32 bits in RV32IM
`define INST_SIZE 31

// RV opcodes are 7 bits
`define OPCODE_SIZE 6

`define DIVIDER_STAGES 8

// Don't forget your old codes
//`include "cla.v"
//`include "DividerUnsignedPipelined.v"

module RegFile (
  input      [        4:0] rd,
  input      [`REG_SIZE:0] rd_data,
  input      [        4:0] rs1,
  output reg [`REG_SIZE:0] rs1_data,
  input      [        4:0] rs2,
  output reg [`REG_SIZE:0] rs2_data,
  input                    clk,
  input                    we,
  input                    rst
);
  localparam NumRegs = 32;
  reg [`REG_SIZE:0] regs[0:NumRegs-1];
  integer i;

  always @(posedge clk) begin
    if (rst) begin
      for (i = 0; i < NumRegs; i = i + 1) begin
        regs[i] <= 0;
      end
    end else if (we && (rd != 0)) begin
      regs[rd] <= rd_data;
    end
  end
    
  // WD Bypass Logic
  always @(*) begin
    if (rs1 == 0) rs1_data = 0;
    else if ((rs1 == rd) && we) rs1_data = rd_data; // Forwarding
    else rs1_data = regs[rs1];
    
    if (rs2 == 0) rs2_data = 0;
    else if ((rs2 == rd) && we) rs2_data = rd_data; // Forwarding
    else rs2_data = regs[rs2];
  end
     // TODO: your code here
endmodule

module DatapathPipelined (
  input                     clk,
  input                     rst,
  output     [ `REG_SIZE:0] pc_to_imem,
  input      [`INST_SIZE:0] inst_from_imem,
  // dmem is read/write
  output reg [ `REG_SIZE:0] addr_to_dmem,
  input      [ `REG_SIZE:0] load_data_from_dmem,
  output reg [ `REG_SIZE:0] store_data_to_dmem,
  output reg [         3:0] store_we_to_dmem,
  output reg                halt,
  // The PC of the inst currently in Writeback. 0 if not a valid inst.
  output reg [ `REG_SIZE:0] trace_writeback_pc,
  // The bits of the inst currently in Writeback. 0 if not a valid inst.
  output reg [`INST_SIZE:0] trace_writeback_inst
);

  // opcodes - see section 19 of RiscV spec
  localparam [`OPCODE_SIZE:0] OpcodeLoad    = 7'b00_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeStore   = 7'b01_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeBranch  = 7'b11_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeJalr    = 7'b11_001_11;
//  localparam [`OPCODE_SIZE:0] OpcodeMiscMem = 7'b00_011_11;
  localparam [`OPCODE_SIZE:0] OpcodeJal     = 7'b11_011_11;

  localparam [`OPCODE_SIZE:0] OpcodeRegImm  = 7'b00_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeRegReg  = 7'b01_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeEnviron = 7'b11_100_11;

  localparam [`OPCODE_SIZE:0] OpcodeAuipc   = 7'b00_101_11;
  localparam [`OPCODE_SIZE:0] OpcodeLui     = 7'b01_101_11;
  
  // ALU operations
  localparam ALU_ADD  = 0;
  localparam ALU_SUB  = 1;
  localparam ALU_AND  = 2;
  localparam ALU_OR   = 3;
  localparam ALU_XOR  = 4;
  localparam ALU_SLL  = 5;
  localparam ALU_SRL  = 6;
  localparam ALU_SRA  = 7;
  localparam ALU_SLT  = 8;
  localparam ALU_SLTU = 9;
  localparam ALU_MUL  = 10;
  localparam ALU_MULH = 11;
  localparam ALU_MULHSU = 12;
  localparam ALU_MULHU  = 13;
  localparam ALU_DIV    = 14;
  localparam ALU_DIVU   = 15;
  localparam ALU_REM    = 16;
  localparam ALU_REMU   = 17;
  localparam ALU_LUI    = 18;
  localparam ALU_AUIPC  = 19;
  localparam ALU_JAL    = 20;
  localparam ALU_JALR   = 21;

  // Branch types
  localparam BR_NONE = 0;
  localparam BR_EQ   = 1;
  localparam BR_NE   = 2;
  localparam BR_LT   = 3;
  localparam BR_GE   = 4;
  localparam BR_LTU  = 5;
  localparam BR_GEU  = 6;

  // Load types
  localparam LD_NONE = 0;
  localparam LD_LB   = 1;
  localparam LD_LH   = 2;
  localparam LD_LW   = 3;
  localparam LD_LBU  = 4;
  localparam LD_LHU  = 5;

  // Store types
  localparam ST_NONE = 0;
  localparam ST_SB   = 1;
  localparam ST_SH   = 2;
  localparam ST_SW   = 3;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  reg [`REG_SIZE:0] cycles_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end
    // --- HAZARD CONTROL SIGNALS ---
  reg stall_F, stall_D, stall_X;
  reg flush_D, flush_X, flush_M;
  
  // Forwarding Signals
  reg [1:0] forward_a; // 00:Reg, 01:WB, 10:MEM
  reg [1:0] forward_b;
  
  reg [7:0] div_valid_pipe;      // Đánh dấu có lệnh Div đang chạy ở stage 0->7
  reg [4:0] div_rd_pipe [0:7];   // Lưu thanh ghi đích (rd) của lệnh Div đó
  reg [7:0] div_is_rem_pipe;     // Lưu xem đó là lệnh lấy dư (REM) hay lấy thương
  reg [7:0] div_quot_neg_pipe;   // Lưu dấu kết quả
  reg [7:0] div_rem_neg_pipe;    
  integer k;                     
  
  reg [7:0]  div_by_zero_pipe;
  reg [7:0]  div_overflow_pipe; 
  reg [31:0] div_orig_op1_pipe [0:7]; 
  /***************/
  /*1. FETCH STAGE */
  /***************/
// branch from X
  reg  [`REG_SIZE:0] f_pc_current;
  wire [`REG_SIZE:0] f_pc_next;
  wire [`REG_SIZE:0] f_inst;
  
  //Branch/Jump from X
  wire x_pc_src;         
  wire [`REG_SIZE:0] x_pc_target;

  assign f_pc_next = (x_pc_src) ? x_pc_target : (f_pc_current + 4);
  // program counter
  always @(posedge clk) begin
    if (rst) begin
      f_pc_current <= 32'd0;
    end else if(!stall_F) begin
      f_pc_current <= f_pc_next;
    end
  end
    // send PC to imem
    assign pc_to_imem = f_pc_current;
    assign f_inst = inst_from_imem;
        
    // PIPELINE REGISTER: F -> D
    reg [`REG_SIZE:0] d_pc;
    reg [`INST_SIZE:0] d_inst;

    always @(posedge clk) begin
        if (rst || flush_D) begin
            d_pc   <= 0;
            d_inst <= 32'h00000013; // NOP (addi x0, x0, 0)
        end else if (!stall_D) begin
            d_pc   <= f_pc_current;
            d_inst <= f_inst;
        end
    end
  /****************/
  /* 2. DECODE STAGE */
  /****************/
    wire [6:0] d_opcode = d_inst[6:0];
    wire [4:0] d_rd     = d_inst[11:7];
    wire [2:0] d_funct3 = d_inst[14:12];
    wire [4:0] d_rs1    = d_inst[19:15];
    wire [4:0] d_rs2    = d_inst[24:20];
    wire [6:0] d_funct7 = d_inst[31:25];
    
    wire [31:0] d_imm_i = {{20{d_inst[31]}}, d_inst[31:20]};
    wire [31:0] d_imm_s = {{20{d_inst[31]}}, d_inst[31:25], d_inst[11:7]};
    wire [31:0] d_imm_b = {{19{d_inst[31]}}, d_inst[31], d_inst[7], d_inst[30:25], d_inst[11:8], 1'b0};
    wire [31:0] d_imm_j = {{11{d_inst[31]}}, d_inst[31], d_inst[19:12], d_inst[20], d_inst[30:21], 1'b0};
    wire [31:0] d_imm_u = {d_inst[31:12], 12'b0};
    
    // Control Unit (Decode)
  reg d_reg_we, d_mem_we, d_mem_rd;
  reg d_alu_src_b_imm;
  reg d_is_branch, d_is_jump;
  reg [4:0] d_alu_op;
  reg [2:0] d_branch_op;
  reg [2:0] d_load_type;   
  reg [1:0] d_store_type;
  reg d_is_div_op;
  reg d_is_ecall;
    always @(*) begin
    // Default Values
    d_reg_we = 0; d_mem_we = 0; d_mem_rd = 0; d_alu_src_b_imm = 0;
    d_is_branch = 0; d_is_jump = 0; d_is_div_op = 0; d_is_ecall = 0;
    d_alu_op = ALU_ADD; d_branch_op = BR_NONE; d_load_type = LD_NONE; d_store_type = ST_NONE;
    case (d_opcode)
      OpcodeRegReg: begin
        d_reg_we = 1;
        // Check M-extension
        if (d_funct7 == 1) begin
          case(d_funct3)
            3'b000: d_alu_op = ALU_MUL;
            3'b001: d_alu_op = ALU_MULH;
            3'b010: d_alu_op = ALU_MULHSU;
            3'b011: d_alu_op = ALU_MULHU;
            3'b100: begin d_alu_op = ALU_DIV;  d_is_div_op = 1; end
            3'b101: begin d_alu_op = ALU_DIVU; d_is_div_op = 1; end
            3'b110: begin d_alu_op = ALU_REM;  d_is_div_op = 1; end
            3'b111: begin d_alu_op = ALU_REMU; d_is_div_op = 1; end
            default:;
          endcase
        end else begin
          // Standard ALU
          case(d_funct3)
            3'b000: d_alu_op = (d_funct7[5]) ? ALU_SUB : ALU_ADD;
            3'b001: d_alu_op = ALU_SLL;
            3'b010: d_alu_op = ALU_SLT;
            3'b011: d_alu_op = ALU_SLTU;
            3'b100: d_alu_op = ALU_XOR;
            3'b101: d_alu_op = (d_funct7[5]) ? ALU_SRA : ALU_SRL;
            3'b110: d_alu_op = ALU_OR;
            3'b111: d_alu_op = ALU_AND;
            default:;
          endcase
        end
      end
      OpcodeRegImm: begin
        d_reg_we = 1;
        d_alu_src_b_imm = 1;
        case(d_funct3)
            3'b000: d_alu_op = ALU_ADD; // ADDI
            3'b010: d_alu_op = ALU_SLT; // SLTI
            3'b011: d_alu_op = ALU_SLTU; // SLTIU
            3'b100: d_alu_op = ALU_XOR; // XORI
            3'b110: d_alu_op = ALU_OR;  // ORI
            3'b111: d_alu_op = ALU_AND; // ANDI
            3'b001: d_alu_op = ALU_SLL; // SLLI
            3'b101: d_alu_op = (d_funct7[5]) ? ALU_SRA : ALU_SRL; // SRAI/SRLI
            default: ;
        endcase
      end
      OpcodeLoad: begin
        d_reg_we = 1;
        d_mem_rd = 1;
        d_alu_src_b_imm = 1;
        d_alu_op = ALU_ADD; // Calculate Addr
        case(d_funct3)
            3'b000: d_load_type = LD_LB;
            3'b001: d_load_type = LD_LH;
            3'b010: d_load_type = LD_LW;
            3'b100: d_load_type = LD_LBU;
            3'b101: d_load_type = LD_LHU;
            default: ;
        endcase
      end
      OpcodeStore: begin
        d_mem_we = 1;
        d_alu_src_b_imm = 1;
        d_alu_op = ALU_ADD; 
        case(d_funct3)
            3'b000: d_store_type = ST_SB;
            3'b001: d_store_type = ST_SH;
            3'b010: d_store_type = ST_SW;
            default: ;
        endcase
      end
      OpcodeLui: begin
        d_reg_we = 1;
        d_alu_op = ALU_LUI;
        d_alu_src_b_imm = 1;
      end
      OpcodeAuipc: begin
        d_reg_we = 1;
        d_alu_op = ALU_AUIPC;
        d_alu_src_b_imm = 1;
      end
      OpcodeBranch: begin
        d_is_branch = 1;
        case(d_funct3)
            3'b000: d_branch_op = BR_EQ;
            3'b001: d_branch_op = BR_NE;
            3'b100: d_branch_op = BR_LT;
            3'b101: d_branch_op = BR_GE;
            3'b110: d_branch_op = BR_LTU;
            3'b111: d_branch_op = BR_GEU;
            default: ;
        endcase
      end
      OpcodeJal: begin
        d_reg_we = 1;
        d_is_jump = 1;
        d_alu_op = ALU_JAL;
        d_alu_src_b_imm = 1;
      end
      OpcodeJalr: begin
        d_reg_we = 1;
        d_is_jump = 1;
        d_alu_op = ALU_JALR;
        d_alu_src_b_imm = 1;
      end
      OpcodeEnviron: begin if (d_inst[31:7] == 0) d_is_ecall = 1; end
      default: ;
    endcase
  end
    // RegFile Interface
  wire [31:0] d_rs1_data_raw, d_rs2_data_raw;
  wire [31:0] w_wb_data;  
  reg        w_reg_we;   
  reg [4:0]  w_rd;       

  wire div_done = div_valid_pipe[7]; 
  wire [4:0] div_done_rd = div_rd_pipe[7];
  wire [31:0] div_quot_u;
  wire [31:0] div_rem_u;
  
  wire [31:0] div_final_quot = div_quot_neg_pipe[7] ? (~div_quot_u + 1) : div_quot_u;
  wire [31:0] div_final_rem  = div_rem_neg_pipe[7] ? (~div_rem_u + 1) : div_rem_u;
  reg [31:0] div_wb_data_val;
  always @(*) begin
      if (div_by_zero_pipe[7]) begin
          // Case 1: Chia cho 0
          if (div_is_rem_pipe[7]) 
              div_wb_data_val = div_orig_op1_pipe[7]; // REM by 0 -> Trả về Dividend gốc
          else 
              div_wb_data_val = 32'hFFFFFFFF;         // DIV by 0 -> Trả về -1
      end else if (div_overflow_pipe[7] && !div_is_rem_pipe[7]) begin
          // Case 2: Tràn số (Chỉ DIV bị, REM thì không)
          // -2^31 / -1 -> Trả về -2^31
          div_wb_data_val = 32'h80000000;
      end else begin
          // Case 3: Bình thường
          div_wb_data_val = div_is_rem_pipe[7] ? div_final_rem : div_final_quot;
      end
  end
  wire [31:0] div_wb_data = div_wb_data_val;

  // MUX: Nếu Divider xong thì ghi Divider, ngược lại ghi Stage W
  wire final_we   = div_done ? 1'b1 : w_reg_we;
  wire [4:0] final_rd = div_done ? div_done_rd : w_rd;
  wire [31:0] final_wb_data = div_done ? div_wb_data : w_wb_data;
  
  reg div_wb_valid_r;
  reg [4:0] div_wb_rd_r;
  reg [31:0] div_wb_data_r;
  
  always @(posedge clk) begin
      if (rst) begin
          div_wb_valid_r <= 0;
          div_wb_rd_r <= 0;
          div_wb_data_r <= 0;
      end else begin
          div_wb_valid_r <= div_done; // div_done lấy từ div_valid_pipe[7]
          div_wb_rd_r    <= div_done_rd;
          div_wb_data_r  <= div_wb_data; //luu kq chia để phòng trường hợp cần dùng lại mà bị mất do qua chu kì kế
      end
  end

  RegFile rf (
    .clk(clk), .rst(rst), 
    .we(final_we),       
    .rd(final_rd),     
    .rd_data(final_wb_data),
    .rs1(d_rs1), .rs1_data(d_rs1_data_raw),
    .rs2(d_rs2), .rs2_data(d_rs2_data_raw)
  );

  // Bypass logic
  wire [`REG_SIZE:0] d_rs1_data_norm = (d_rs1 != 0 && d_rs1 == w_rd && w_reg_we) ? w_wb_data : d_rs1_data_raw;
  wire [`REG_SIZE:0] d_rs2_data_norm = (d_rs2 != 0 && d_rs2 == w_rd && w_reg_we) ? w_wb_data : d_rs2_data_raw;

  // Ưu tiên 1: Lấy ngay từ output của Divider (Stage 7) nếu vừa tính xong
  // Ưu tiên 2: Lấy từ Buffer (nếu bị lệch 1 nhịp)
  // Ưu tiên 3: Lấy bình thường
  wire [`REG_SIZE:0] d_rs1_data = 
        (div_done && d_rs1 == div_done_rd && d_rs1 != 0) ? div_wb_data : 
        (div_wb_valid_r && d_rs1 == div_wb_rd_r && d_rs1 != 0) ? div_wb_data_r : 
        d_rs1_data_norm;

  wire [`REG_SIZE:0] d_rs2_data = 
        (div_done && d_rs2 == div_done_rd && d_rs2 != 0) ? div_wb_data : 
        (div_wb_valid_r && d_rs2 == div_wb_rd_r && d_rs2 != 0) ? div_wb_data_r : 
        d_rs2_data_norm;
  // immediate
  reg [31:0] d_imm;
  always @(*) begin
    if (d_opcode == OpcodeStore) d_imm = d_imm_s;
    else if (d_opcode == OpcodeBranch) d_imm = d_imm_b;
    else if (d_opcode == OpcodeJal) d_imm = d_imm_j;
    else if (d_opcode == OpcodeLui || d_opcode == OpcodeAuipc) d_imm = d_imm_u;
    else d_imm = d_imm_i; // Load, ALU Imm, Jalr
  end

    // PIPELINE REGISTER: D -> X
  reg [31:0] x_pc, x_rs1_data, x_rs2_data, x_imm;
  reg [31:0] x_inst;
  reg [4:0]  x_rd, x_rs1, x_rs2;
  reg [2:0]  x_funct3;
  reg [6:0]  x_funct7;
  reg [6:0]  x_opcode;
  
  reg x_reg_we, x_mem_we, x_mem_rd, x_alu_src_b_imm;
  reg x_is_branch, x_is_jump, x_is_div_op, x_is_ecall;
  reg [4:0] x_alu_op;
  reg [2:0] x_branch_op;
  reg [2:0] x_load_type;
  reg [1:0] x_store_type;

  // wire forwarding
  wire [31:0] x_op1_val; 
  wire [31:0] x_op2_val;

  always @(posedge clk) begin
    if (rst || flush_X) begin
      x_reg_we <= 0; x_mem_we <= 0; x_mem_rd <= 0; x_is_branch <= 0; x_is_jump <= 0;
      x_inst <= 32'h13; x_is_div_op <= 0; x_is_ecall <= 0;
      x_load_type <= LD_NONE; x_store_type <= ST_NONE;
      x_pc <= 0; x_imm <= 0;
    end else if (stall_X) begin
      if (forward_a != 2'b00) x_rs1_data <= x_op1_val;
      if (forward_b != 2'b00) x_rs2_data <= x_op2_val;
    end else begin
      // NORMAL LOAD
      x_pc <= d_pc; x_inst <= d_inst;
      x_rs1_data <= d_rs1_data; x_rs2_data <= d_rs2_data;
      x_imm <= d_imm;
      x_rd <= d_rd; x_rs1 <= d_rs1; x_rs2 <= d_rs2;
      x_funct3 <= d_funct3; x_funct7 <= d_funct7; x_opcode <= d_opcode;
      x_reg_we <= d_reg_we; x_mem_we <= d_mem_we; x_mem_rd <= d_mem_rd;
      x_alu_src_b_imm <= d_alu_src_b_imm;
      x_alu_op <= d_alu_op; x_branch_op <= d_branch_op;
      x_is_branch <= d_is_branch; x_is_jump <= d_is_jump;
      x_is_div_op <= d_is_div_op;
      x_load_type <= d_load_type; x_store_type <= d_store_type;
      x_is_ecall <= d_is_ecall;
    end
  end
  // ========================================================================
  // 3. EXECUTE STAGE (X)
  // ========================================================================
  
  // --- Forwarding Logic (Bypass) ---
  reg [31:0] m_alu_result; 
  reg        m_reg_we;
  reg [4:0]  m_rd;

  wire use_div_fwd_a = (div_valid_pipe[7] && div_rd_pipe[7] != 0 && div_rd_pipe[7] == x_rs1);
  wire use_div_fwd_b = (div_valid_pipe[7] && div_rd_pipe[7] != 0 && div_rd_pipe[7] == x_rs2);

  assign x_op1_val = use_div_fwd_a ? div_wb_data :           // Ưu tiên 1: Lấy từ Divider ngay lập tức
                     (forward_a == 2'b10) ? m_alu_result : 
                     (forward_a == 2'b01) ? w_wb_data : x_rs1_data;

  assign x_op2_val = use_div_fwd_b ? div_wb_data :         
                     (forward_b == 2'b10) ? m_alu_result : 
                     (forward_b == 2'b01) ? w_wb_data : x_rs2_data;
  
  // ALU Inputs
  wire [31:0] alu_in1 = (x_alu_op == ALU_AUIPC || x_alu_op == ALU_JAL || x_alu_op == ALU_JALR) ? x_pc : x_op1_val;
  wire [31:0] alu_in2 = (x_alu_src_b_imm) ? x_imm : x_op2_val;
  // CLA for ADD
  wire [31:0] cla_sum;
  cla u_cla (
    .a(alu_in1),
    .b(alu_in2),
    .cin(1'b0),   
    .sum(cla_sum)
  );
  // --- ALU ---
  reg [31:0] x_alu_result_normal;
  always @(*) begin
    case (x_alu_op)
        ALU_ADD:  x_alu_result_normal = cla_sum;
        ALU_SUB:  x_alu_result_normal = alu_in1 - alu_in2;
        ALU_AND:  x_alu_result_normal = alu_in1 & alu_in2;
        ALU_OR:   x_alu_result_normal = alu_in1 | alu_in2;
        ALU_XOR:  x_alu_result_normal = alu_in1 ^ alu_in2;
        ALU_SLL:  x_alu_result_normal = alu_in1 << alu_in2[4:0];
        ALU_SRL:  x_alu_result_normal = alu_in1 >> alu_in2[4:0];
        ALU_SRA:  x_alu_result_normal = $signed(alu_in1) >>> alu_in2[4:0];
        ALU_SLT:  x_alu_result_normal = ($signed(alu_in1) < $signed(alu_in2)) ? 1 : 0;
        ALU_SLTU: x_alu_result_normal = (alu_in1 < alu_in2) ? 1 : 0;
        ALU_MUL:  x_alu_result_normal = alu_in1 * alu_in2;
        ALU_MULH: x_alu_result_normal = ($signed({{32{alu_in1[31]}}, alu_in1}) * $signed({{32{alu_in2[31]}}, alu_in2})) >> 32;
        ALU_MULHSU: x_alu_result_normal = ($signed({{32{alu_in1[31]}}, alu_in1}) * $signed({32'b0, alu_in2})) >> 32;
        ALU_MULHU: x_alu_result_normal = ({{32'b0}, alu_in1} * {{32'b0}, alu_in2}) >> 32;
        ALU_LUI:   x_alu_result_normal = x_imm;
        ALU_AUIPC: x_alu_result_normal = x_pc + x_imm;
        ALU_JAL, ALU_JALR: x_alu_result_normal = x_pc + 4; 
        default: x_alu_result_normal = 0;
    endcase
  end
  

  // Divider  
	reg [31:0] div_op1_latched, div_op2_latched; //chot du lieu tranh bi nhieu loan du lieu khi qua chu ky moi
  
  wire current_quot_neg = x_op1_val[31] ^ x_op2_val[31];
  wire current_rem_neg  = x_op1_val[31];
  
  wire [31:0] abs_rs1 = ((x_alu_op == ALU_DIV || x_alu_op == ALU_REM) && x_op1_val[31]) ? (~x_op1_val + 1) : x_op1_val;
  wire [31:0] abs_rs2 = ((x_alu_op == ALU_DIV || x_alu_op == ALU_REM) && x_op2_val[31]) ? (~x_op2_val + 1) : x_op2_val;

  // 3. Pipeline Tracking & Latching Inputs
  always @(posedge clk) begin
    if (rst) begin
        div_valid_pipe <= 0;
        div_op1_latched <= 0;
        div_op2_latched <= 0;
        div_by_zero_pipe <= 0;
        div_overflow_pipe <= 0;
    end else if (!stall_X) begin
        div_valid_pipe[7:1] <= div_valid_pipe[6:0];
        
        div_rd_pipe[7] <= div_rd_pipe[6]; div_rd_pipe[6] <= div_rd_pipe[5];
        div_rd_pipe[5] <= div_rd_pipe[4]; div_rd_pipe[4] <= div_rd_pipe[3];
        div_rd_pipe[3] <= div_rd_pipe[2]; div_rd_pipe[2] <= div_rd_pipe[1];
        div_rd_pipe[1] <= div_rd_pipe[0];

        div_orig_op1_pipe[7] <= div_orig_op1_pipe[6]; div_orig_op1_pipe[6] <= div_orig_op1_pipe[5];
        div_orig_op1_pipe[5] <= div_orig_op1_pipe[4]; div_orig_op1_pipe[4] <= div_orig_op1_pipe[3];
        div_orig_op1_pipe[3] <= div_orig_op1_pipe[2]; div_orig_op1_pipe[2] <= div_orig_op1_pipe[1];
        div_orig_op1_pipe[1] <= div_orig_op1_pipe[0];

        div_is_rem_pipe[7:1]   <= div_is_rem_pipe[6:0];
        div_quot_neg_pipe[7:1] <= div_quot_neg_pipe[6:0];
        div_rem_neg_pipe[7:1]  <= div_rem_neg_pipe[6:0];
        div_by_zero_pipe[7:1]  <= div_by_zero_pipe[6:0];
        div_overflow_pipe[7:1] <= div_overflow_pipe[6:0];

        // 2. Load New Instruction from Stage X
        if (x_is_div_op) begin
            div_valid_pipe[0] <= 1'b1;
            div_rd_pipe[0]    <= x_rd;
            div_orig_op1_pipe[0] <= x_op1_val;
            
            div_op1_latched   <= abs_rs1;
            div_op2_latched   <= abs_rs2;

            div_is_rem_pipe[0]<= (x_alu_op == ALU_REM || x_alu_op == ALU_REMU);
            div_quot_neg_pipe[0] <= (x_alu_op == ALU_DIV || x_alu_op == ALU_REM) ? current_quot_neg : 0;
            div_rem_neg_pipe[0]  <= (x_alu_op == ALU_DIV || x_alu_op == ALU_REM) ? current_rem_neg : 0;
            
            div_by_zero_pipe[0]  <= (x_op2_val == 0);
            div_overflow_pipe[0] <= (x_alu_op == ALU_DIV || x_alu_op == ALU_REM) && 
                                    (x_op1_val == 32'h80000000) && (x_op2_val == 32'hFFFFFFFF);
        end else begin
            div_valid_pipe[0] <= 1'b0;
            div_rd_pipe[0] <= 0;
            div_by_zero_pipe[0] <= 0;
            div_overflow_pipe[0] <= 0;
        end
    end else begin //when stall keep going but ko nap lenh
        div_valid_pipe[7:1] <= div_valid_pipe[6:0];
        
        div_rd_pipe[7] <= div_rd_pipe[6]; div_rd_pipe[6] <= div_rd_pipe[5];
        div_rd_pipe[5] <= div_rd_pipe[4]; div_rd_pipe[4] <= div_rd_pipe[3];
        div_rd_pipe[3] <= div_rd_pipe[2]; div_rd_pipe[2] <= div_rd_pipe[1];
        div_rd_pipe[1] <= div_rd_pipe[0];

        div_orig_op1_pipe[7] <= div_orig_op1_pipe[6]; div_orig_op1_pipe[6] <= div_orig_op1_pipe[5];
        div_orig_op1_pipe[5] <= div_orig_op1_pipe[4]; div_orig_op1_pipe[4] <= div_orig_op1_pipe[3];
        div_orig_op1_pipe[3] <= div_orig_op1_pipe[2]; div_orig_op1_pipe[2] <= div_orig_op1_pipe[1];
        div_orig_op1_pipe[1] <= div_orig_op1_pipe[0];

        div_is_rem_pipe[7:1] <= div_is_rem_pipe[6:0];
        div_quot_neg_pipe[7:1] <= div_quot_neg_pipe[6:0];
        div_rem_neg_pipe[7:1] <= div_rem_neg_pipe[6:0];
        div_by_zero_pipe[7:1] <= div_by_zero_pipe[6:0];
        div_overflow_pipe[7:1] <= div_overflow_pipe[6:0];
        
        div_valid_pipe[0] <= 0;
    end
  end

  DividerUnsignedPipelined divider (
    .clk(clk), .rst(rst), .stall(1'b0),
    .i_dividend(div_op1_latched), 
    .i_divisor(div_op2_latched),
    .o_remainder(div_rem_u), 
    .o_quotient(div_quot_u)
  );
  
  wire [31:0] x_alu_result = x_alu_result_normal;
 //Branch
  reg take_branch;
  always @(*) begin
      case(x_branch_op)
         BR_EQ: take_branch = (x_op1_val == x_op2_val); 
         BR_NE: take_branch = (x_op1_val != x_op2_val); 
         BR_LT: take_branch = ($signed(x_op1_val) < $signed(x_op2_val)); 
         BR_GE: take_branch = ($signed(x_op1_val) >= $signed(x_op2_val)); 
         BR_LTU: take_branch = (x_op1_val < x_op2_val); 
         BR_GEU: take_branch = (x_op1_val >= x_op2_val); 
         default: take_branch = 0;
      endcase
  end
  
  assign x_pc_src = (x_is_branch && take_branch) || x_is_jump;
  assign x_pc_target = (x_opcode == OpcodeJalr) ? (x_op1_val + x_imm) & ~1 : (x_pc + x_imm);

  // ========================================================================
  // PIPELINE REGISTER: X -> M
  // ========================================================================
  reg [31:0] m_pc, m_store_data, m_inst;
  reg m_mem_we, m_mem_rd, m_is_ecall;
  reg [2:0] m_load_type;
  reg [1:0] m_store_type;

  always @(posedge clk) begin
      if (rst || flush_M) begin
          m_reg_we <= 0; m_mem_we <= 0; m_mem_rd <= 0; m_inst <= 32'h13; m_is_ecall <= 0;
          m_load_type <= LD_NONE; m_store_type <= ST_NONE;
          m_alu_result <= 0; // Clear data to avoid stale forwarding
      end else begin
          m_pc <= x_pc;
          m_inst <= x_inst;
          m_alu_result <= x_alu_result;
          m_store_data <= x_op2_val; 
          m_rd <= x_rd;
          m_reg_we <= (x_is_div_op) ? 1'b0 : x_reg_we;
          m_mem_we <= x_mem_we;
          m_mem_rd <= x_mem_rd;
          m_load_type <= x_load_type;
          m_store_type <= x_store_type;
          m_is_ecall <= x_is_ecall;
      end
  end

  // 4. MEMORY STAGE (M)
  always @(*) begin
      addr_to_dmem = m_alu_result;
      // Store Data Alignment
      case (m_alu_result[1:0])
        2'b00: store_data_to_dmem = m_store_data;
        2'b01: store_data_to_dmem = m_store_data << 8;
        2'b10: store_data_to_dmem = m_store_data << 16;
        2'b11: store_data_to_dmem = m_store_data << 24;
      endcase
      // Store Mask
      store_we_to_dmem = 0;
      if (m_mem_we) begin
         if (m_store_type == ST_SB) store_we_to_dmem = 4'b0001 << m_alu_result[1:0]; 
         else if (m_store_type == ST_SH) store_we_to_dmem = (m_alu_result[1] ? 4'b1100 : 4'b0011); 
         else store_we_to_dmem = 4'b1111; 
      end
  end

  // PIPELINE REGISTER: M -> W
  reg [31:0] w_pc, w_alu_result, w_mem_data, w_inst;
  reg [2:0] w_load_type;
  reg w_mem_rd, w_is_ecall;

  always @(posedge clk) begin
      if (rst) begin
          w_reg_we <= 0; w_inst <= 32'h13; w_is_ecall <= 0;
      end else begin
          w_pc <= m_pc;
          w_inst <= m_inst;
          w_alu_result <= m_alu_result;
          w_mem_data <= load_data_from_dmem;
          w_rd <= m_rd;
          w_reg_we <= m_reg_we;
          w_mem_rd <= m_mem_rd;
          w_load_type <= m_load_type;
          w_is_ecall <= m_is_ecall;
      end
  end
  // 5. WRITEBACK STAGE (W)
  // Load Data Alignment
  reg [31:0] loaded_val;
  reg [7:0]  lb_byte;
  reg [15:0] lh_half;

  always @(*) begin
      case(w_alu_result[1:0])
        2'b00: lb_byte = w_mem_data[7:0];
        2'b01: lb_byte = w_mem_data[15:8];
        2'b10: lb_byte = w_mem_data[23:16];
        2'b11: lb_byte = w_mem_data[31:24];
      endcase
      lh_half = w_alu_result[1] ? w_mem_data[31:16] : w_mem_data[15:0];

      case(w_load_type)
         LD_LB: loaded_val = {{24{lb_byte[7]}}, lb_byte};
         LD_LH: loaded_val = {{16{lh_half[15]}}, lh_half};
         LD_LW: loaded_val = w_mem_data;
         LD_LBU: loaded_val = {24'b0, lb_byte};
         LD_LHU: loaded_val = {16'b0, lh_half};
         default: loaded_val = w_mem_data;
      endcase
  end

  assign w_wb_data = w_mem_rd ? loaded_val : w_alu_result;
  // Trace
  always @(*) begin
      trace_writeback_pc = w_pc;
      trace_writeback_inst = w_inst;
      halt = w_is_ecall;
  end
  // ========================================================================
  // HAZARD UNIT
  // ========================================================================
  always @(*) begin
      // 1. Forwarding Logic
      if (m_reg_we && (m_rd != 0) && (m_rd == x_rs1)) forward_a = 2'b10;
      else if (w_reg_we && (w_rd != 0) && (w_rd == x_rs1)) forward_a = 2'b01;
      else forward_a = 2'b00;
      
      if (m_reg_we && (m_rd != 0) && (m_rd == x_rs2)) forward_b = 2'b10;
      else if (w_reg_we && (w_rd != 0) && (w_rd == x_rs2)) forward_b = 2'b01;
      else forward_b = 2'b00;

      // Reset Control Signals
      stall_F = 0; stall_D = 0; flush_D = 0;
      flush_X = 0; stall_X = 0; flush_M = 0;

      // 2. Load-Use Stall
      if (x_mem_rd && (x_rd != 0) && (x_rd == d_rs1 || x_rd == d_rs2)) begin
          stall_F = 1; stall_D = 1; flush_X = 1;
      end
      
      // DIVIDER HAZARD LOGIC
      // A. Check Hazard for div instr in Pipeline
      for (k=0; k<6; k=k+1) begin
          if (div_valid_pipe[k] && div_rd_pipe[k] != 0 && 
             (div_rd_pipe[k] == d_rs1 || div_rd_pipe[k] == d_rs2)) begin
              stall_F = 1; stall_D = 1; flush_X = 1;
          end
      end

      // B. RAW Hazard: Check Stage X
      if (x_is_div_op && x_rd != 0 && (x_rd == d_rs1 || x_rd == d_rs2)) begin
          stall_F = 1; stall_D = 1; flush_X = 1;
      end

      // C. Ordering Hazard: Stall lệnh thường (Non-Div)
      if ((x_is_div_op || (|div_valid_pipe[5:0])) && !d_is_div_op && !d_is_ecall) begin
          stall_F = 1; stall_D = 1; flush_X = 1;
      end

      // 4. Control Hazard
      if (x_pc_src) begin
          flush_D = 1; flush_X = 1;
          stall_F = 0; stall_D = 0; stall_X = 0; // Clear stall if branch taken
      end
  end
  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

endmodule

module MemorySingleCycle #(
    parameter NUM_WORDS = 512
) (
    input                    rst,                 // rst for both imem and dmem
    input                    clk,                 // clock for both imem and dmem
	                                              // The memory reads/writes on @(negedge clk)
    input      [`REG_SIZE:0] pc_to_imem,          // must always be aligned to a 4B boundary
    output reg [`REG_SIZE:0] inst_from_imem,      // the value at memory location pc_to_imem
    input      [`REG_SIZE:0] addr_to_dmem,        // must always be aligned to a 4B boundary
    output reg [`REG_SIZE:0] load_data_from_dmem, // the value at memory location addr_to_dmem
    input      [`REG_SIZE:0] store_data_to_dmem,  // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input      [        3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];

  // preload instructions to mem_array
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end

  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  always @(negedge clk) begin
    inst_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end

  always @(negedge clk) begin
    if (store_we_to_dmem[0]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
    end
    if (store_we_to_dmem[1]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
    end
    if (store_we_to_dmem[2]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
    end
    if (store_we_to_dmem[3]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
    end
    // dmem is "read-first": read returns value before the write
    load_data_from_dmem <= mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];
  end
endmodule

/* This design has just one clock for both processor and memory. */
 module Processor (
    input                 clk,
    input                 rst,
    output                halt,
    output [ `REG_SIZE:0] trace_writeback_pc,
    output [`INST_SIZE:0] trace_writeback_inst
);

  wire [`INST_SIZE:0] inst_from_imem;
  wire [ `REG_SIZE:0] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [         3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
    .rst                 (rst),
    .clk                 (clk),
    // imem is read-only
    .pc_to_imem          (pc_to_imem),
    .inst_from_imem      (inst_from_imem),
    // dmem is read-write
    .addr_to_dmem        (mem_data_addr),
    .load_data_from_dmem (mem_data_loaded_value),
    .store_data_to_dmem  (mem_data_to_write),
    .store_we_to_dmem    (mem_data_we)
  );

  DatapathPipelined datapath (
    .clk                  (clk),
    .rst                  (rst),
    .pc_to_imem           (pc_to_imem),
    .inst_from_imem       (inst_from_imem),
    .addr_to_dmem         (mem_data_addr),
    .store_data_to_dmem   (mem_data_to_write),
    .store_we_to_dmem     (mem_data_we),
    .load_data_from_dmem  (mem_data_loaded_value),
    .halt                 (halt),
    .trace_writeback_pc   (trace_writeback_pc),
    .trace_writeback_inst (trace_writeback_inst)
  );

endmodule




