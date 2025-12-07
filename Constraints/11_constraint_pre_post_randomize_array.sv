/* 
 * File Name      : 11_constraint_pre_post_randomize_array.sv
 * Date           : 07-12-2025
 * Description    : Pre- and post-randomize example
 *                  len in [5:12]
 *                  data_q.size() == len
 *                  data_q elements inside [0:99]
 *                  pre_randomize() forces first element to 0 if array allocated
 *                  post_randomize() prints array and counts elements > 50
 * Copyright      : Open for educational and non-commercial use
 * Permission     : Permission granted to use, modify and distribute this file 
 *                  with proper reference to the author
 * Author         : Hemanth Sekhar
 * Email          : khsekhar9@gmail.com
 */

class constraint_hs_11;
  rand byte data_q[];
  rand int unsigned len;
  int count;

  constraint c1 {
    len inside {[5:12]};
    data_q.size() == len;
    foreach (data_q[i]) data_q[i] inside {[0:99]};
  }

  function void pre_randomize();
    if (data_q.size() > 0)
      data_q[0] = 0;
  endfunction

  function void post_randomize();
    count = 0;
    foreach (data_q[i]) begin
      $display(" data_q[%0d] = %0d", i, data_q[i]);
      if (data_q[i] > 50)
        count++;
    end
    $display("No of elements greater than 50 = %0d", count);
  endfunction
endclass


module top;
  constraint_hs_11 cons = new();
  initial begin
    repeat (5) begin
      assert (cons.randomize())
        else $fatal("Randomization failed");
    end
  end
endmodule
