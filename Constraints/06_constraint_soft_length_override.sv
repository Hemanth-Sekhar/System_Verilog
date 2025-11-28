// -----------------------------------------------------------------------------
// File Name   : 06_constraint_soft_length_override.sv
// Date        : 28-11-2025
// Description : Demonstrates use of soft constraints and conditional override
//               behavior on a packet length field. The 'length' field has a
//               preferred soft default while a short-packet flag can tighten
//               the allowed range and override the soft preference. The
//               payload size is derived from the length to show arithmetic
//               relationships in constraints.
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
  • Randomize:
        length      → 16-bit total packet length (bytes), range [64:512]
        payload[]   → dynamic array of bytes
        is_short_pkt→ flag indicating a short packet
  • Constraints:
        – length inside [64:512] as a hard range
        – soft length == 128 as a preferred default
        – length must be a multiple of 4
        – payload.size() == length / 4
        – if is_short_pkt == 1 → length inside [64:96]
        – if is_short_pkt == 0 → soft default (128) may be used or any valid
          value in the allowed range that satisfies all constraints
  • Randomize multiple times and print:
        is_short_pkt, length, payload.size(), and length/4
    to verify the relationship between fields and soft override behavior.
*/

class constraint_hs_6;
  rand logic [15:0] length;
  rand logic [7:0]  payload[];
  rand bit          is_short_pkt;

  constraint c_len {
    length inside {[64:512]};
    soft length == 128;
  }

  constraint c_payload {
    length % 4 == 0;
    payload.size() == length / 4;
  }

  constraint c_short {
    if (is_short_pkt)
      length inside {[64:96]};
  }
endclass

module top;
  constraint_hs_6 con_hs = new();

  initial begin
    repeat (10) begin
      assert(con_hs.randomize());
      $display("is_short_pkt=%0b, length=%0d, payload.size=%0d (length/4=%0d)",con_hs.is_short_pkt, con_hs.length,con_hs.payload.size(), con_hs.length/4);
    end
  end
endmodule
