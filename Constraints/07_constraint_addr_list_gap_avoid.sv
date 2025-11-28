// -----------------------------------------------------------------------------
// File Name   : 07_constraint_addr_list_gap_avoid.sv
// Date        : 28-11-2025
// Description : Randomizes a dynamic array of addresses with constraints on
//               size, valid range, ascending order with minimum spacing,
//               avoidance of reserved regions, and a soft preference toward
//               lower address range. Demonstrates foreach-based array CRV with
//               hard and soft constraints combined.
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
Constraint Question:
  • Randomize addr_list[] (dynamic array of 10-bit addresses 0–1023)
  • Apply constraints:
        – addr_list.size() inside [4:8]
        – each element inside [0:511]
        – strictly ascending: addr_list[i] > addr_list[i-1]
        – minimum spacing: addr_list[i] - addr_list[i-1] >= 8
        – avoid ranges: [32:63], [128:159], [256:271]
        – soft preference for addresses inside [0:255]
  • Randomize multiple times and print size and contents for validation
*/

class constraint_hs_7;
  rand logic [9:0] addr_list[];

  constraint c {
    addr_list.size() inside {[4:8]};

    foreach (addr_list[i])
      addr_list[i] inside {[0:511]};

    foreach (addr_list[i])
      if (i > 0)
        addr_list[i] - addr_list[i-1] >= 8;

    foreach (addr_list[i])
      !(addr_list[i] inside {[32:63], [128:159], [256:271]});

    foreach (addr_list[i])
      soft addr_list[i] inside {[0:255]};
  }
endclass

module top;
  constraint_hs_7 con_hs = new();

  initial begin
    repeat (10) begin
      assert(con_hs.randomize());
      $display("size=%0d, addr_list=%0p",
               con_hs.addr_list.size(), con_hs.addr_list);
    end
  end
endmodule
