// -----------------------------------------------------------------------------
// File Name   : 01_oops_basic.sv
// Date        : 30-11-2025
// Description : Demonstrates basic OOP usage in SystemVerilog using classes and
//               objects. A 'student' class is created with public data members
//               and a print method. An object of the class is instantiated and
//               member variables are assigned before printing in a formatted
//               table layout.
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
OOP Question 1:
  • Create a student class with members: name, id, marks.
  • Create an object of the class and assign values.
  • Print values in a formatted table.
*/

class student;
  string name = "";
  int id;
  int marks;
  
  function void print();
    $display("+-------------------------------------+");
    $display("|    Name    |    ID    |    Marks    |");
    $display("+-------------------------------------+");
    $display("|   %0s   |   %0d   |    %0d     |", name, id, marks);
    $display("+-------------------------------------+");
  endfunction
endclass

module top;
  student harry;

  initial begin
    harry = new();
    harry.name  = "HARRY";
    harry.id    = 1;
    harry.marks = 99;
    harry.print();
  end
endmodule
