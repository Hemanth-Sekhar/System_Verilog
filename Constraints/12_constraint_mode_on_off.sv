/* 
 * File Name      : 12_constraint_mode_on_off.sv
 * Date           : 07-12-2025
 * Description    : Demonstrates constraint_mode ON/OFF control
 *                  a, b, c inside [1:20]
 *                  Sum constraint (a + b + c == 25) enabled for first 3 randomizations
 *                  Sum constraint disabled for next 3 randomizations
 *                  Display values after each randomization to observe behavior change
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

class constraint_hs_12;
  rand int a, b, c;

  constraint c1 { 
    a inside {[1:20]};
    b inside {[1:20]};
    c inside {[1:20]};
  }

  constraint sum_const { 
    a + b + c == 25;
  }

  function void display();
    $display("a = %0d | b = %0d | c = %0d", a, b, c);
  endfunction
endclass


module top;
  constraint_hs_12 cons = new();
  initial begin

    // Constraint ON — sum must be 25
    repeat (3) begin
      assert(cons.randomize());
      cons.display();
    end

    // Turn OFF sum constraint
    cons.sum_const.constraint_mode(0);

    // Constraint OFF — values free from sum rule
    repeat (3) begin
      assert(cons.randomize());
      cons.display();
    end
  end
endmodule
