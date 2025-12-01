// -----------------------------------------------------------------------------
// File Name   : 09_packed_vs_unpacked_arrays.sv
// Date        : 01-12-2025
// Description : Demonstrates the difference between packed and unpacked arrays
//               in SystemVerilog. A 32-bit packed vector 'p' is used to
//               represent 4 concatenated bytes, while 'u' is an unpacked array
//               of 4 separate 8-bit elements. The example shows how $bits()
//               differs for packed vs unpacked arrays, how bit-slicing can be
//               used to move data between them, and how modifying a single
//               element in the unpacked array affects only that element,
//               whereas modifying the packed vector affects the overall bit
//               representation.
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
Array Question 9:
  • Declare a packed array:   logic [31:0] p;
  • Declare an unpacked array: logic [7:0] u[4];
  • Assign 4 distinct byte values into 'u'.
  • Pack the 4 bytes into 'p' using concatenation or bit-slicing.
  • Print:
        - $bits(p)
        - $bits(u)
        - Values of p and u[]
  • Modify u[0] and show that only one element changes.
  • Modify p and show that it affects the entire bit-vector representation.
*/

module top;

  // Packed array: single 32-bit vector (4 bytes packed together)
  logic [31:0] p;

  // Unpacked array: 4 separate 8-bit elements
  logic [7:0]  u[4];

  initial begin
    // Initialize unpacked array elements
    u[0] = 8'h11;
    u[1] = 8'h22;
    u[2] = 8'h33;
    u[3] = 8'h44;

    // Pack the 4 bytes into the 32-bit packed vector
    // p[31:24] = u[3], p[23:16] = u[2], p[15:8] = u[1], p[7:0] = u[0]
    p = {u[3], u[2], u[1], u[0]};

    $display("\n--- Initial Values ---");
    $display("u[0] = 0x%0h, u[1] = 0x%0h, u[2] = 0x%0h, u[3] = 0x%0h",
              u[0], u[1], u[2], u[3]);
    $display("p    = 0x%0h", p);

    // Show $bits for packed vs unpacked
    $display("\n--- $bits Information ---");
    $display("$bits(p)   = %0d", $bits(p));
    $display("$bits(u)   = %0d (array object)", $bits(u));
    $display("$bits(u[0])= %0d (single element)", $bits(u[0]));

    // Modify u[0] only
    $display("\n--- Modify u[0] Only ---");
    u[0] = 8'hAA;
    $display("After u[0] change:");
    $display("u[0] = 0x%0h, u[1] = 0x%0h, u[2] = 0x%0h, u[3] = 0x%0h",
              u[0], u[1], u[2], u[3]);

    // Re-pack into p to reflect the new u[0] value
    p = {u[3], u[2], u[1], u[0]};
    $display("p (re-packed) = 0x%0h", p);

    // Modify the packed vector directly
    $display("\n--- Modify Packed Vector p ---");
    p = 32'hDE_AD_BE_EF;
    $display("p changed to = 0x%0h", p);

    // Unpack p back into u using bit-slicing
    u[0] = p[7:0];
    u[1] = p[15:8];
    u[2] = p[23:16];
    u[3] = p[31:24];

    $display("After unpacking from p:");
    $display("u[0] = 0x%0h, u[1] = 0x%0h, u[2] = 0x%0h, u[3] = 0x%0h\n",
              u[0], u[1], u[2], u[3]);
  end

endmodule
