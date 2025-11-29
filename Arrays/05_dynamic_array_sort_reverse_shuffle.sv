// -----------------------------------------------------------------------------
// File Name   : 05_dynamic_array_sort_reverse_shuffle.sv
// Date        : 29-11-2025
// Description : Demonstrates sorting, reversing, and shuffling operations on a
//               dynamic array of integers in SystemVerilog. The dynamic array
//               is initialized with 12 random values. The array is first sorted
//               in ascending order, then reversed to flip the order of sorted
//               elements, and finally shuffled to produce a random order. The
//               contents of the array are printed after each step to showcase
//               the effect of every transformation.
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
Array Question 5:
  • Create a dynamic array of 12 random integers
  • Sort the array in ascending order
  • Reverse the sorted array
  • Shuffle the reversed array
  • Print the array after each operation
*/

class array_hs_5;
  int dyn_arr[];
endclass


module top;
  array_hs_5 arr = new();

  initial begin
    // Allocate array of size 12
    arr.dyn_arr = new[12];

    // Assign random values
    foreach (arr.dyn_arr[i])
      arr.dyn_arr[i] = $urandom_range(0, 100);

    $display("\nOriginal Array      = %0p", arr.dyn_arr);

    // Sort ascending
    arr.dyn_arr.sort();
    $display("After Sort          = %0p", arr.dyn_arr);

    // Reverse the sorted array
    arr.dyn_arr.reverse();
    $display("After Reverse       = %0p", arr.dyn_arr);

    // Shuffle the reversed array
    arr.dyn_arr.shuffle();
    $display("After Shuffle       = %0p\n", arr.dyn_arr);
  end
endmodule
