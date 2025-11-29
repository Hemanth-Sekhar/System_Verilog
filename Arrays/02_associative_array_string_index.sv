// -----------------------------------------------------------------------------
// File Name   : 02_associative_array_string_index.sv
// Date        : 29-11-2025
// Description : Demonstrates associative array usage indexed by string keys.
//               A register file model is implemented using an associative
//               array where each key ("first", "second", "third", "fourth",
//               "fifth") maps to an 8-bit register value. The contents are
//               printed, then a specific key ("third") is deleted, and the
//               updated contents and count of remaining entries are displayed.
//               This example showcases associative array declaration, value
//               assignment, deletion of a key, foreach traversal, and the
//               num() method in SystemVerilog.
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
Array Question 2:
  • Create an associative array indexed by string to store 5 register values.
  • Print all entries.
  • Delete one key.
  • Print remaining entries and display the total number of elements.
*/

class array_hs_2;
  bit [7:0] asso_arr[string];

  // Initialize 5 entries
  function new();
    asso_arr["first"]  = 1;
    asso_arr["second"] = 2;
    asso_arr["third"]  = 3;
    asso_arr["fourth"] = 4;
    asso_arr["fifth"]  = 5;
  endfunction
endclass


module top;
  array_hs_2 arr = new();

  initial begin
    // Print full associative array before deletion
    $display("\n--- Before Deletion ---");
    $display("%0p", arr.asso_arr);

    // Delete one key
    arr.asso_arr.delete("third");

    // Print individual entries after deletion
    $display("\n--- After Deletion of \"third\" ---");
    foreach (arr.asso_arr[key])
      $display("key = %s, value = %0d", key, arr.asso_arr[key]);

    // Print number of remaining entries
    $display("Total Remaining Entries = %0d\n", arr.asso_arr.num());
  end
endmodule
