// -----------------------------------------------------------------------------
// File Name   : 04_queue_find_methods.sv
// Date        : 29-11-2025
// Description : Demonstrates the use of queue search methods in SystemVerilog.
//               A queue of 20 random integers (0–50) is generated, and the
//               find(), find_first(), and find_last() iterator methods are
//               applied to extract elements greater than 30. The example
//               prints the original queue, the set of all matches, the first
//               match, and the last match to illustrate search capabilities
//               on dynamic data collections.
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
Array Question 4:
  • Create a queue of 20 random integers (0–50)
  • Use find()       → extract all elements > 30
  • Use find_first() → extract the first element > 30
  • Use find_last()  → extract the last element > 30
  • Print original queue and all extracted results
*/

class array_hs_4;
  int que_arr[$];

  // Fill queue with 20 random elements
  function new();
    while (que_arr.size() < 20) begin
      que_arr.push_front($urandom_range(0, 50));
    end
  endfunction
endclass


module top;
  array_hs_4 arr = new();
  int q_all[$];
  int q_first[$];
  int q_last[$];

  initial begin
    $display("\n--- Original Queue ---");
    $display("que_arr = %0p", arr.que_arr);

    // find() → all matches
    q_all = arr.que_arr.find with (item > 30);
    $display("\nElements > 30 (find)       = %0p", q_all);

    // find_first() → first match
    q_first = arr.que_arr.find_first with (item > 30);
    $display("First element > 30         = %0p", q_first);

    // find_last() → last match
    q_last = arr.que_arr.find_last with (item > 30);
    $display("Last element > 30          = %0p", q_last);

    $display("");
  end
endmodule
