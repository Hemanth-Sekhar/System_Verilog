// -----------------------------------------------------------------------------
// File Name   : 06_array_of_objects.sv
// Date        : 30-11-2025
// Description : Demonstrates a dynamic array of class objects in SystemVerilog.
//               A class 'packet' contains 8-bit randomizable address and data
//               fields. A dynamic array of 8 packet objects is allocated,
//               randomized, and printed in a formatted table using a class
//               method. This example highlights dynamic array of objects,
//               object allocation, randomization, and table-style display.
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
Array Question 6:
  • Create a `packet` class with rand addr and data fields.
  • Create a dynamic array of 8 packet objects.
  • Allocate each object (new) and randomize individually.
  • Print the Addr and Data fields in formatted table form.
*/

class packet;
  rand bit [7:0] addr;
  rand bit [7:0] data;

  function void print(int index);
    $display("  %0d   |  %0d   |  %0d", index, addr, data);
  endfunction
endclass


module top;
  packet dyn_arr[];

  initial begin
    dyn_arr = new[8];

    $display("\n Index | Addr | Data");
    $display("---------------------");

    foreach (dyn_arr[i]) begin
      dyn_arr[i] = new();                 // allocate object
      assert(dyn_arr[i].randomize());     // randomize addr+data
      dyn_arr[i].print(i);                // formatted row-wise printing
    end

    $display(""); // line break after table
  end
endmodule
