// -----------------------------------------------------------------------------
// File Name   : 04_oop_shallow_vs_deep_copy.sv
// Date        : 02-12-2025
// Description : Demonstrates shallow copy vs deep copy semantics for class
//               handles in SystemVerilog. A 'packet' class is defined with
//               randomizable addr and data fields. p2 is assigned as a shallow
//               copy of p1, so changes in p2 reflect in p1. p3 is created as a
//               deep copy of p1 by copying each field individually, so changes
//               in p3 do not affect p1.
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

class packet;
  rand bit [7:0] addr;
  rand bit [7:0] data;

  function void print(string tag);
    $display("%s : ADDR = 0x%0h, DATA = 0x%0h", tag, addr, data);
  endfunction
endclass


module top;
  packet p1 = new();
  packet p2; // shallow copy handle
  packet p3; // deep copy object

  initial begin
    assert(p1.randomize());
    $display("\n--- Initial p1 ---");
    p1.print("p1");

    // ----------------- Shallow Copy -----------------
    p2 = p1; // shallow copy (same handle)
    $display("\n--- After Shallow Copy (p2 = p1) ---");
    p1.print("p1");
    p2.print("p2");

    // Modify p2 and show it affects p1
    $display("\n--- Modify p2 (shallow copy) ---");
    p2.addr = 8'hFF;
    p2.data = 8'hAA;
    p1.print("p1 (after p2 change)");
    p2.print("p2 (after change)");

    // ----------------- Deep Copy -----------------
    p3 = new();          // new separate object
    p3.addr = p1.addr;   // field-by-field copy
    p3.data = p1.data;

    $display("\n--- After Deep Copy (p3 from p1) ---");
    p1.print("p1 (before p3 change)");
    p3.print("p3 (before change)");

    // Modify p3 and show p1 is unaffected
    $display("\n--- Modify p3 (deep copy) ---");
    p3.addr = 8'h11;
    p3.data = 8'h22;

    p1.print("p1 (after p3 change)");
    p3.print("p3 (after change)\n");
  end
endmodule
