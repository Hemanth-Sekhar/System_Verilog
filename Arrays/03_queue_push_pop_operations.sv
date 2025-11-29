// -----------------------------------------------------------------------------
// File Name   : 03_queue_push_pop_operations.sv
// Date        : 29-11-2025
// Description : Demonstrates queue usage with push and pop operations. A queue
//               of integers is populated with 10 random values using push_back,
//               and values are then popped until only 4 elements remain. The
//               example prints the number of pushes, number of pops, and the
//               final queue contents. This exercise highlights queue operations
//               such as push_back(), pop_front(), size(), and traversal in
//               SystemVerilog.
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
Array Question 3:
  • Create a queue of integers
  • Push 10 random values
  • Pop elements until only 4 remain
  • Print total pushes, total pops, and final queue contents
*/

class array_hs_3;
  int que_arr[$];
endclass


module top;
  array_hs_3 arr = new();

  initial begin
    int push_count = 0;
    int pop_count  = 0;

    // Push 10 random values
    repeat (10) begin
      arr.que_arr.push_back($urandom_range(0, 100));
      push_count++;
    end

    $display("\n--- Queue After Pushes ---");
    $display("Push Count = %0d", push_count);
    $display("Contents   = %0p", arr.que_arr);

    // Pop until 4 entries remain
    while (arr.que_arr.size() > 4) begin
      arr.que_arr.pop_front();
      pop_count++;
    end

    $display("\n--- Final Queue State ---");
    $display("Final Pop Count = %0d", pop_count);
    $display("Final Contents  = %0p", arr.que_arr);
    $display("Final Size      = %0d\n", arr.que_arr.size());
  end
endmodule
