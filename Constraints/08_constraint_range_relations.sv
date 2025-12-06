// -----------------------------------------------------------------------------
// File Name   : 08_constraint_range_relations.sv
// Date        : 06-12-2025
// Description : Advanced constraint example for three related variables a, b, c.
//               Demonstrates range constraint, relational constraints, and an
//               arithmetic relation across variables:
//                 - a inside [10:50]
//                 - a < b < c
//                 - (c - a) == 20
//               Randomization is repeated multiple times to observe solutions.
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

class range_rel;
  rand int a, b, c;

  // a is in [10:50], a < b < c, and c - a is fixed to 20
  constraint c1 {
    a inside {[10:50]};
    a < b;
    b < c;
    (c - a) == 20;
  }

  function void display();
    $display("[%0t] a = %0d, b = %0d, c = %0d", $time, a, b, c);
  endfunction
endclass


module top;
  range_rel rang;

  initial begin
    rang = new();

    // Try multiple randomizations to observe different valid solutions
    repeat (5) begin
      if (!rang.randomize()) begin
        $error("[%0t] Randomization failed for range_rel", $time);
      end
      else begin
        rang.display();
      end
    end

    $finish;
  end
endmodule
