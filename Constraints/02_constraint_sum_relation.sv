// -----------------------------------------------------------------------------
// File Name   : 02_constraint_sum_relation.sv
// Date        : 28-11-2025
// Description : Randomizes three variables 'a', 'b', and 'c' and applies a
//               mathematical constraint that forces 'c' to always be equal to
//               the sum of 'a' and 'b'. This demonstrates how arithmetic
//               relationships can be encoded inside SystemVerilog constraints
//               and validated through randomization.
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
  • Randomize three variables:
        a → 4-bit value (0–15)
        b → 4-bit value (0–15)
        c → 5-bit value (0–31)
  • Apply constraint: c must always be equal to (a + b)
  • Randomize the object multiple times and print a, b, and c values
    to verify that the arithmetic constraint holds.
*/

class constraint_hs_2;
  rand logic [3:0] a;
  rand logic [3:0] b;
  rand logic [4:0] c;

  constraint c1 {
    c == a + b;   
  }
endclass

module top;
  constraint_hs_2 con_hs = new();

  initial begin
    repeat (5) begin
      assert(con_hs.randomize());
      $display("a = %0d, b = %0d, c = %0d (a + b = %0d)", con_hs.a, con_hs.b, con_hs.c, con_hs.a + con_hs.b);
    end
  end
endmodule
