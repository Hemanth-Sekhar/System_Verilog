// -----------------------------------------------------------------------------
// File Name   : 01_dynamic_array_resizing.sv
// Date        : 29-11-2025
// Description : Demonstrates dynamic array randomization and resizing without
//               losing existing contents. The 'dyn_arr' is randomized with a
//               size between 5 and 12. After randomization, the array is
//               resized to +3 elements and later resized again to -2 elements
//               using the copy-resize mechanism (new[](...)) to preserve data.
//               This example illustrates size constraints, CRV for arrays,
//               and safe dynamic array resizing in SystemVerilog.
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
  • Randomize a dynamic array of 2-bit values:
        dyn_arr[] → each element is logic [1:0] (range 0–3)
  • Constraints:
        – dyn_arr.size() must be between 5 and 12
  • After randomization:
        – Increase size by +3 while retaining existing elements
        – Decrease size by −2 while still preserving elements
  • Print size and contents (before resize, after +3, after −2)
*/

class array_hs_1;
  rand logic [1:0] dyn_arr[];

  // size constraint between 5 and 12
  constraint c1 { soft dyn_arr.size() inside {[5:12]}; }
endclass


module top;
  array_hs_1 arr = new();

  initial begin
    // First randomization
    assert(arr.randomize());

    $display("\nBefore Resizing:");
    $display("Size = %0d, Contents = %0p", arr.dyn_arr.size(), arr.dyn_arr);

    // Resize +3 : preserve previous values
    arr.dyn_arr = new[arr.dyn_arr.size()+3](arr.dyn_arr);

    $display("\nAfter Resizing +3:");
    $display("Size = %0d, Contents = %0p", arr.dyn_arr.size(), arr.dyn_arr);

    // Resize -2 : preserve values
    arr.dyn_arr = new[arr.dyn_arr.size()-2](arr.dyn_arr);

    $display("\nAfter Resizing -2:");
    $display("Size = %0d, Contents = %0p\n", arr.dyn_arr.size(), arr.dyn_arr);
  end
endmodule
