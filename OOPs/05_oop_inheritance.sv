// -----------------------------------------------------------------------------
// File Name   : 05_oop_inheritance.sv
// Date        : 03-12-2025
// Description : Demonstrates inheritance in SystemVerilog OOP. The child class
//               'student' inherits members and methods from the parent class
//               'person'. The child constructor calls the parent constructor
//               using super.new to initialize inherited fields. Three student
//               objects are created and displayed using the overridden print()
//               method which builds on the parent print() method.
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

class person;
  string name;
  int age;

  function new(string name, int age);
    this.name = name;
    this.age  = age;
  endfunction

  function void print();
    $display("Name  = %0s", name);
    $display("Age   = %0d", age);
  endfunction
endclass


class student extends person;
  int marks;

  function new(string name, int age, int marks);
    super.new(name, age);   // call the parent constructor
    this.marks = marks;
  endfunction

  function void print();
    super.print();                      // print parent fields
    $display("Marks = %0d\n", marks);   // append child field
  endfunction
endclass


module top;
  student ram;
  student ravi;
  student nani;

  initial begin
    ram  = new("RAM",  22, 98);
    ravi = new("RAVI", 22, 91);
    nani = new("NANI", 21, 89);

    ram.print();
    ravi.print();
    nani.print();
  end
endmodule
