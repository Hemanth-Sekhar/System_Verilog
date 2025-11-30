// -----------------------------------------------------------------------------
// File Name   : 07_associative_array_navigation.sv
// Date        : 30-11-2025
// Description : Demonstrates associative array navigation using first(), next(),
//               last(), and prev() methods in SystemVerilog. An associative
//               array indexed by int holds random 8-bit values at sparse,
//               non-sequential indices between 0 and 100. The contents are
//               printed from lowest to highest index using first/next and then
//               from highest to lowest index using last/prev, illustrating
//               ordered traversal of associative arrays.
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
Array Question 7:
  • Create an associative array indexed by int storing random 8-bit values.
  • Insert values at 10 random sparse indices between 0 and 100.
  • Print all entries in ascending index order using first()/next().
  • Print all entries in descending index order using last()/prev().
  • Do not use foreach for navigation.
*/

class array_hs_7;
  // associative array: index = int, value = 8-bit
  bit [7:0] asso_arr[int];

  // Initialize with 10 sparse random entries
  function void init_sparse();
    int idx;
    repeat (10) begin
      idx = $urandom_range(0, 100);
      asso_arr[idx] = $urandom_range(0, 255);
    end
  endfunction
endclass


module top;
  array_hs_7 arr = new();

  initial begin
    int idx;

    // Insert 10 sparse entries
    arr.init_sparse();

    // Ascending traversal using first/next
    $display("\n--- Associative Array (Ascending: first/next) ---");
    if (arr.asso_arr.first(idx)) begin
      do begin
        $display("index = %0d -> value = %0d", idx, arr.asso_arr[idx]);
      end while (arr.asso_arr.next(idx));
    end
    else begin
      $display("Associative array is empty.");
    end

    // Descending traversal using last/prev
    $display("\n--- Associative Array (Descending: last/prev) ---");
    if (arr.asso_arr.last(idx)) begin
      do begin
        $display("index = %0d -> value = %0d", idx, arr.asso_arr[idx]);
      end while (arr.asso_arr.prev(idx));
    end
    else begin
      $display("Associative array is empty.");
    end

    $display("");
  end
endmodule
