// -----------------------------------------------------------------------------
// File Name   : 04_constraint_sorted_dynamic_array.sv
// Date        : 28-11-2025
// Description : Demonstrates constraint usage on a dynamic array of bytes. The
//               'data' array is randomized with a size between 5 and 10, and
//               its elements are constrained to form a strictly ascending
//               sequence with additional bounds on the first and last elements.
//               This example showcases foreach-based indexing and array size
//               constraints in SystemVerilog CRV.
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
  • Randomize a dynamic array:
        data[] → each element is 8-bit (0–255)
  • Apply constraints:
        – data.size() must be between 5 and 10
        – data must be strictly ascending (data[i] > data[i-1] for i > 0)
        – data[0] must be >= 20
        – data[data.size()-1] must be <= 200
  • Randomize multiple times and print the size and contents of 'data'
    to observe the behavior of the ascending sequence and bounds.
*/

class constraint_hs_4;
  rand logic [7:0] data[];

  constraint c1 {
    // size between 5 and 10
    data.size() inside {[5:10]};

    // strictly ascending sequence
    foreach (data[i]) {
      if (i > 0)
        data[i] > data[i-1];
    }

    // value bounds on first and last elements
    data[0]          >= 20;
    data[data.size()-1] <= 200;
  }
endclass

module top;
  constraint_hs_4 con_hs = new();

  initial begin
    repeat (8) begin
      assert(con_hs.randomize());
      $display("size = %0d, data = %0p", con_hs.data.size(), con_hs.data);
    end
  end
endmodule
