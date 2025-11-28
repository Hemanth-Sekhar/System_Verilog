// -----------------------------------------------------------------------------
// File Name   : 03_constraint_unique_values.sv
// Date        : 28-11-2025
// Description : Randomizes five 4-bit variables (d0–d4) and applies constraints
//               to ensure that all values are unique and that d0 is always the
//               smallest among them. This example demonstrates the use of the
//               'unique' constraint and relational ordering within SV CRV.
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
  • Randomize five variables:
        d0, d1, d2, d3, d4 → each is a 4-bit value (0–15)
  • Apply constraints:
        – All five values must be UNIQUE
        – d0 must always be the smallest value among all
  • Randomize multiple times and print the values to confirm uniqueness
    and ordering behavior.
*/

class constraint_hs_3;
  rand logic [3:0] d0, d1, d2, d3, d4;

  constraint c1 {
    unique {d0, d1, d2, d3, d4};  // no repetition allowed
    d0 < d1;
    d0 < d2;
    d0 < d3;
    d0 < d4;                      // enforce d0 as smallest
  }
endclass

module top;
  constraint_hs_3 con_hs = new();

  initial begin
    repeat (5) begin
      assert(con_hs.randomize());
      $display("d0=%0d, d1=%0d, d2=%0d, d3=%0d, d4=%0d",con_hs.d0, con_hs.d1, con_hs.d2, con_hs.d3, con_hs.d4);
    end
  end
endmodule
