// -----------------------------------------------------------------------------
// File Name   : 02_oop_student_encapsulation.sv
// Date        : 02-12-2025
// Description : Demonstrates encapsulation using a student class in
//               SystemVerilog. Data members are kept local while getter and
//               setter methods are used for controlled access. Three student
//               objects are created and initialized using setters, and their
//               details are displayed via a print() method.
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
  local int    id;
  local int    marks;

  function void set_name(string name);
    this.name = name;
  endfunction

  function void set_id(int id);
    this.id = id;
  endfunction

  function void set_marks(int marks);
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
    harry  = new();
    dustin = new();
    mike   = new();

    harry.set_name("HARRY");
    harry.set_id(202501);
    harry.set_marks(96);

    dustin.set_name("DUSTIN");
    dustin.set_id(202502);
    dustin.set_marks(91);

    mike.set_name("MIKE");
    mike.set_id(202503);
    mike.set_marks(92);

    harry.print();
    dustin.print();
    mike.print();
  end
endmodule
