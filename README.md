# 5-Stage Pipelined RISC-V Processor (RV32IM)

![Language](https://img.shields.io/badge/Language-Verilog%2FSystemVerilog-blue)
![Architecture](https://img.shields.io/badge/Architecture-RISC--V_RV32IM-red)
![Pipeline](https://img.shields.io/badge/Pipeline-5_Stage-orange)
![Tool](https://img.shields.io/badge/Tool-Vivado_%7C_GTKWave-green)

## 📌 Overview

This project implements a fully synthesizable **32-bit RISC-V Processor** based on the **RV32IM** Instruction Set Architecture. The core features a classic **5-stage pipeline** designed for high throughput, integrated with custom-designed hardware arithmetic units including a **Hierarchical Carry Lookahead Adder (CLA)** and a **Non-blocking Pipelined Divider**.

The design features a robust **Hazard Detection Unit** that handles Data Hazards, Control Hazards, and Structural Hazards entirely in hardware, eliminating the need for software NOPs.

---

## 🚀 Key Features

* **ISA Support:** RV32IM (Integer + Multiplication/Division).
* **Pipeline Structure:** 5 Stages (IF, ID, EX, MEM, WB).
* **Hazard Management:**
    * **Data Forwarding:** Solves Read-After-Write (RAW) hazards by forwarding data from EX/MEM and MEM/WB stages directly to the ALU.
    * **Load-Use Stalling:** Automatically detects and stalls the pipeline for 1 cycle when a Load instruction is followed by a dependent instruction.
    * **Branch Flushing:** Handles control hazards by flushing the pipeline upon branch misprediction.
* **Custom Arithmetic Units:**
    * **Hierarchical CLA:** A 32-bit adder built using a `gp8` -> `gp4` -> `gp1` hierarchical structure for optimized carry propagation.
    * **Pipelined Divider:** A multi-cycle divider that allows the processor to execute independent instructions while division is in progress (Latency Hiding).

---

## 🏗️ Architecture Design

The processor follows the standard 5-stage pipeline organization:

| Stage | Description |
| :--- | :--- |
| **1. IF (Instruction Fetch)** | Fetches instructions from Instruction Memory using the Program Counter (PC). |
| **2. ID (Instruction Decode)** | Decodes opcodes, reads from the Register File, and generates control signals. This stage also contains the **Hazard Unit** for stall/flush logic. |
| **3. EX (Execute)** | Performs arithmetic/logic operations. This stage instantiates the custom **CLA** module and the **Pipelined Divider**. It also handles branch comparison and target calculation. |
| **4. MEM (Memory)** | Accesses Data Memory for Load (`LW`, `LB`, etc.) and Store (`SW`, `SB`, etc.) instructions. |
| **5. WB (Writeback)** | Writes the execution result or memory data back to the Register File. |

### 🧩 Hierarchical Carry Lookahead Adder (CLA)
Instead of using the standard `+` operator, the ALU utilizes a custom CLA module for integer addition. The design is hierarchical:
1.  **gp1 (Bit-level):** Computes Generate (`g`) and Propagate (`p`) for single bits.
2.  **gp4 (Group-level):** Instantiates 4 `gp1` modules to compute Lookahead Carry for a 4-bit block.
3.  **gp8 (Block-level):** Instantiates 2 `gp4` modules to handle 8-bit blocks.
4.  **cla (Top-level):** Connects 4 `gp8` blocks to form a full 32-bit adder.

### ➗ Pipelined Hardware Divider
The division unit is designed as a separate pipeline parallel to the main ALU.
* **Mechanism:** It computes the quotient and remainder over multiple cycles.
* **Non-blocking:** The main pipeline only stalls if an instruction tries to read the division result before it is ready. Otherwise, subsequent instructions continue execution.

---

## ⚡ Hazard Handling Details

### 1. Data Hazards (RAW)
* **Forwarding:** Data is bypassed from the end of the EX stage or the end of the MEM stage back to the EX stage input.
    * *Scenario:* `ADD x1, x2, x3` -> `SUB x4, x1, x5`. The result of `x1` is forwarded to `SUB` immediately.
* **Stalling:** Used strictly for **Load-Use** cases where forwarding is impossible due to memory latency.

### 2. Control Hazards
* **Prediction:** The processor assumes "Branch Not Taken".
* **Correction:** If the branch condition is met (Taken) in the EX stage, the **ID** and **IF** stages are flushed (reset to NOPs), and the PC is updated to the branch target.

---

## 📝 Supported Instructions

The processor supports the **RV32IM** subset:

### RV32I (Base Integer)
* **Arithmetic:** `ADD`, `SUB`, `ADDI`, `LUI`, `AUIPC`
* **Logical:** `AND`, `OR`, `XOR`, `ANDI`, `ORI`, `XORI`
* **Shifts:** `SLL`, `SRL`, `SRA`, `SLLI`, `SRLI`, `SRAI`
* **Compare:** `SLT`, `SLTU`, `SLTI`, `SLTIU`
* **Control:** `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `JAL`, `JALR`
* **Memory:** `LW`, `SW`, `LB`, `SB`, `LH`, `SH`, `LBU`, `LHU`

### RV32M (Multiplication Extension)
* **Multiply:** `MUL`, `MULH`, `MULHSU`, `MULHU`
* **Divide:** `DIV`, `DIVU`, `REM`, `REMU`

---
## How to Run

1.  **Clone the repository:**
2.  **Open in Vivado:**
    * Create a new project.
    * Add all design files (`.v`) and the memory file (`.hex`).
    * Set `tb_pipelined.v` as the simulation top module.
3.  **Run Simulation:**
    * Run Behavioral Simulation.
    * Observe the waveforms for `trace_pc`, `trace_inst`, and register values.

## Acknowledgements
This project was developed for the **Introduction to System-on-Chip (SoC)** course.
