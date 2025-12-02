// -----------------------------------------------------------------------------
// File Name   : 06_oop_method_overriding_polymorphism.sv
// Date        : 02-12-2025
// Description : Demonstrates method overriding and runtime polymorphism in
//               SystemVerilog OOP. A parent class 'shape' defines a virtual
//               method area(), which is overridden in child classes 'circle',
//               'square', and 'rectangle'. A single parent-class handle is used
//               to invoke overridden implementations dynamically, showcasing
//               polymorphism behavior crucial in verification/UVM.
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

class shape;
  // Using virtual enables run-time polymorphism
  virtual function void area();
    $display("Base shape: area not defined");
  endfunction
endclass


class circle extends shape;
  int radius;

  function new(int r);
    radius = r;
  endfunction

  // Overridden method
  virtual function void area();
    real a = 3.14 * radius * radius;
    $display("Circle (r=%0d) -> Area = %0f", radius, a);
  endfunction
endclass


class square extends shape;
  int side;

  function new(int s);
    side = s;
  endfunction

  // Overridden method
  virtual function void area();
    int a = side * side;
    $display("Square (side=%0d) -> Area = %0d", side, a);
  endfunction
endclass


class rectangle extends shape;
  int length;
  int width;

  function new(int l, int w);
    length = l;
    width  = w;
  endfunction

  // Overridden method
  virtual function void area();
    int a = length * width;
    $display("Rectangle (%0dx%0d) -> Area = %0d", length, width, a);
  endfunction
endclass



module top;
  shape s;               // Parent handle
  circle    c  = new(5); // radius = 5
  square    sq = new(4); // side   = 4
  rectangle r  = new(6,3); // 6 × 3

  initial begin
    $display("\n---- Runtime Polymorphism Demo ----");

    s = c;
    s.area();   // Executes circle.area()

    s = sq;
    s.area();   // Executes square.area()

    s = r;
    s.area();   // Executes rectangle.area()

    $display("-----------------------------------\n");
  end
endmodule
