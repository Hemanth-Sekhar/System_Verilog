/* 
 * File Name      : 13_constraint_inline_randc_failure_handling.sv
 * Date           : 07-12-2025
 * Description    : Demonstrates randc, inline constraints, and randomization
 *                  failure handling.
 *                  - id is randc [3:0] (cyclic)
 *                  - priority_hs inside [0:10]
 *                  - timeout inside [10:100]
 *                  In TB:
 *                    * 20 iterations of randomize() with inline constraints:
 *                        priority_hs > 5  -> timeout < 50
 *                        priority_hs <= 5 -> timeout >= 50
 *                    * On failure, print error and continue
 *                    * On success, display id, priority_hs, timeout each time
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

class constraint_hs_13;
  randc bit [3:0] id;
  rand int unsigned priority_hs;
  rand int unsigned timeout;

  constraint c1 {
    priority_hs inside {[0:10]};
    timeout     inside {[10:100]};
  }

  function void display();
    $display("id = %0d | priority_hs = %0d | timeout = %0d",
             id, priority_hs, timeout);
  endfunction
endclass


module top;
  constraint_hs_13 cons = new();

  initial begin
    repeat (20) begin
      if (!cons.randomize() with {
            (priority_hs > 5)  -> (timeout < 50);
            (priority_hs <= 5) -> (timeout >= 50);
          })
        $display("RANDOMIZATION FAILED");
      else
        cons.display();
    end
  end
endmodule
