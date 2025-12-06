// -----------------------------------------------------------------------------
// File Name   : 07_oop_inheritance_polymorphism.sv
// Date        : 06-12-2025
// Description : Demonstrates inheritance, constructor calling using super.new(),
//               method overriding in child class, and runtime polymorphism by
//               using a parent-class handle to call the overridden method in
//               the child class.
//               
//               This OOP concept is widely used in UVM for base class reuse
//               and dynamic method dispatch during runtime.
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

class packet;
  logic [31:0] addr;
  logic [31:0] data;
  
  function new(logic [31:0] addr, logic [31:0] data);
    this.addr = addr;
    this.data = data;
  endfunction
  
  virtual function void display();
    $display("[PARENT] Addr = %0h, Data = %0h", addr, data);
  endfunction
endclass


class write_packet extends packet;
  logic write_enable;
  
  function new(logic [31:0] addr, logic [31:0] data, logic we);
    super.new(addr, data);
    this.write_enable = we;
  endfunction

  function void display();
    $display("[CHILD ] Addr = %0h, Data = %0h, WE = %0b",
             addr, data, write_enable);
  endfunction
endclass


module top;
  packet       pkt;
  write_packet w_pkt;

  initial begin
    w_pkt = new(12, 13, 1);
    pkt  = w_pkt;       // parent handle → child object
    pkt.display();      // runtime polymorphism
  end
endmodule
