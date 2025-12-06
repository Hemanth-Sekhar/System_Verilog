/* 
 * File Name      : 09_sum_rel_advanced_constraints.sv
 * Date           : 06-12-2025
 * Description    : Advanced constraint relation — x, y, z in [0:30], sum == 40,
 *                  all values unique, and no variable is more than 2× any other.
 *                  After randomization, print the values and identify the largest.
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : hemanthsekharofficial@gmail.com
 */

class range;
  rand int x, y, z;

  constraint c1 { 
    x inside {[0:30]};
    y inside {[0:30]};
    z inside {[0:30]};
    (x + y + z) == 40;
    x < 2*y;
    x < 2*z;
    y < 2*x;
    y < 2*z;
    z < 2*x;
    z < 2*y;
    unique {x, y, z};
  }

  function void post_randomize();
    if (x > y && x > z)
      $display("X is largest - %0d", x);
    else if (y > x && y > z)
      $display("Y is largest - %0d", y);
    else
      $display("Z is largest - %0d", z);
  endfunction

  function void display();
    $display("x = %0d, y = %0d, z = %0d", x, y, z);
  endfunction
endclass


module top;
  range rang = new();
  
  initial begin
    assert(rang.randomize());
    rang.display();
  end
endmodule
