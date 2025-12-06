// -----------------------------------------------------------------------------
// File Name   : 08_oop_pure_virtual_abstract_class.sv
// Date        : 06-12-2025
// Description : Demonstrates pure virtual method, abstract class behavior,
//               overriding in child class, and runtime polymorphism using a
//               parent-class handle to a child-class object in SystemVerilog.
//               
//               The base class 'packet' declares a pure virtual display()
//               method, making it abstract. The derived class 'write_packet'
//               implements display(), and a parent handle is used to call the
//               overridden method dynamically.
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
  
  // pure virtual → no body, must be implemented by child
  pure virtual function void display();
endclass


class write_packet extends packet;
  logic write_enable;
  
  function new(logic [31:0] addr, logic [31:0] data, logic we);
    super.new(addr, data);
    this.write_enable = we;
  endfunction

  function void display();
    $display("Addr          = %0h", addr);
    $display("Data          = %0h", data);
    $display("write_enable  = %0h", write_enable);
  endfunction
endclass


module top;
  packet       pkt;    // abstract base-class handle
  write_packet w_pkt;  // concrete derived-class object

  initial begin
    w_pkt = new(32'h12, 32'h34, 1'b1);
    pkt   = w_pkt;      // parent handle → child object (polymorphism)
    pkt.display();      // calls write_packet::display()
  end
endmodule
