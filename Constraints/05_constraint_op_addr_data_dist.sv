// -----------------------------------------------------------------------------
// File Name   : 05_constraint_op_addr_data_dist.sv
// Date        : 28-11-2025
// Description : Demonstrates the use of weighted randomization (dist) and
//               integrated conditional constraints linking opcode (op),
//               address, and data. For each opcode, the allowed address range
//               and data pattern are enforced through implication-style
//               constraints in a compact form.
//
// Copyright (c) 2025 Hemanth Sekhar
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this HDL source file to use, copy, modify, merge, publish, or distribute
// it for educational or non-commercial purposes, provided that this notice is
// included in all copies or substantial portions of the file.
//
// THIS HDL SOURCE FILE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// FUNCTIONAL CORRECTNESS, PERFORMANCE, OR FITNESS FOR A PARTICULAR PURPOSE.
//
// Author      : Hemanth Sekhar
// Email       : khsekhar9@gmail.com
// -----------------------------------------------------------------------------

/*
Constraint Question:
  • Randomize:
        op   → 2-bit opcode: 0 = IDLE, 1 = READ, 2 = WRITE
        addr → 10-bit address: 0–1023
        data → 8-bit payload: 0–255
  • Apply constraints:
        – Weighted distribution on op:
              IDLE  → 20%
              READ  → 40%
              WRITE → 40%
        – Combined conditional behavior per opcode:
              if op == READ  → addr in [0:255]   & data odd
              if op == WRITE → addr in [256:511] & data even
              if op == IDLE  → addr in [0:1023]  & data = 0
  • Randomize several times and print results to observe the enforced mappings.
*/

class constraint_hs_5;
  rand logic [1:0] op;      // 0 = IDLE, 1 = READ, 2 = WRITE
  rand logic [9:0] addr;    // 0–1023
  rand logic [7:0] data;    // 0–255

  constraint c1 {
    // Weighted opcode selection
    op dist { 0 := 20, 1 := 40, 2 := 40 };

    // Integrated conditional constraints
    (op == 1) -> (addr inside {[0:255]}   && (data % 2 != 0));   // READ
    (op == 2) -> (addr inside {[256:511]} && (data % 2 == 0));   // WRITE
    (op == 0) -> (addr inside {[0:1023]}  && (data == 0));       // IDLE
  }
endclass

module top;
  constraint_hs_5 con_hs = new();

  function string op_to_string(logic [1:0] op);
    case (op)
      2'd0: op_to_string = "IDLE";
      2'd1: op_to_string = "READ";
      2'd2: op_to_string = "WRITE";
      default: op_to_string = "UNKNOWN";
    endcase
  endfunction

  initial begin
    repeat (10) begin
      assert(con_hs.randomize());
      $display("op=%0d (%s), addr=%0d, data=%0d",
               con_hs.op, op_to_string(con_hs.op),
               con_hs.addr, con_hs.data);
    end
  end
endmodule
