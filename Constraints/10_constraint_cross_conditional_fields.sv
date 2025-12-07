/* 
 * File Name      : 10_constraint_cross_conditional_fields.sv
 * Date           : 07-12-2025
 * Description    : Cross-conditional constraints on addr, data, write_enable.
 *                  addr in [0:200]
 *                  If write_enable == 1  → data in [50:100]
 *                  If write_enable == 0  → data == 0
 *                  If MSB of addr is 1   → write_enable must be 1
 *                  Post-randomize prints values.
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

class constraint_hs_10;
  rand bit [7:0] addr;
  rand bit [7:0] data;
  rand bit write_enable;

  constraint c1 { 
    addr inside {[0:200]};
    write_enable == 1 -> data inside {[50:100]};
    write_enable == 0 -> data == 0;
    addr[7] == 1 -> write_enable == 1;
  }

  function void post_randomize();
    $display("addr=%0h | data=%0h | write_enable=%0h", addr, data, write_enable);
  endfunction
endclass


module top;
  constraint_hs_10 cons = new();
  initial begin
    assert (cons.randomize())
      else $fatal("Randomization failed");
  end
endmodule
