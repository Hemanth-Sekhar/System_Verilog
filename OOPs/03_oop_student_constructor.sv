// -----------------------------------------------------------------------------
// File Name   : 03_oop_student_constructor.sv
// Date        : 02-12-2025
// Description : Demonstrates the use of constructors in SystemVerilog OOP.
//               Class members are encapsulated and initialized through a
//               parameterized constructor. Three student objects are created
//               using the constructor and displayed using the print() method,
//               which internally calls getter methods.
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

class student;
  local string name = "";
  local int id;
  local int marks;

  function new(string name, int id, int marks);
    this.name  = name;
    this.id    = id;
    this.marks = marks;
  endfunction

  function string get_name();
    return this.name;
  endfunction

  function int get_id();
    return this.id;
  endfunction

  function int get_marks();
    return this.marks;
  endfunction

  function void print();
    $display("Name  = %0s", get_name());
    $display("ID    = %0d", get_id());
    $display("Marks = %0d\n", get_marks());
  endfunction
endclass


module top;
  student harry;
  student dustin;
  student mike;

  initial begin
    harry  = new("HARRY",  202501, 96);
    dustin = new("DUSTIN", 202503, 94);
    mike   = new("MIKE",   202504, 89);

    harry.print();
    dustin.print();
    mike.print();
  end
endmodule
