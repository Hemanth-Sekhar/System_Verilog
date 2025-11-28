// -----------------------------------------------------------------------------
// File Name   : 01_constraint_using_conditional_or_implication_operator.sv
// Date        : 28-11-2025
// Description : Demonstrates conditional constraint linking between 'mode' and
//               'value' using a compact ternary operator. If mode = 0, value
//               ranges from 0–100; otherwise (mode = 1), value ranges from
//               100–255. The constraint is written in a minimal, clean form
//               using the conditional (?:) operator instead of implication (->).
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

class constraint_hs_1;
  rand logic       mode;      // 0 or 1
  rand logic [7:0] value;     // 0–255

  // Constraint written using conditional (ternary) operator 
  constraint c1 {
    value inside { (mode == 0) ? [0:100] : [100:255] };
  }
  /*  Constraint written using Implication operator
  constraint c1 { 
  (mode == 0) -> value inside {[0:100]};
  (mode == 1) -> value inside {[100:255]};
    }
  */
  
endclass

module top;
  constraint_hs_1 con_hs = new();

  initial begin
    repeat (5) begin
      assert(con_hs.randomize());
      $display("%p", con_hs);
    end
  end
endmodule
