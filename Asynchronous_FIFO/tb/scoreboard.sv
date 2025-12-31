class scoreboard;

  // expected data queue (FIFO model)
  logic [7:0] exp_q[$];   

  packet pkt;
  logic [7:0] exp_data;

  task run();
    forever begin
      // get event from monitor (write or read)
      common::mon2scb.get(pkt);

      // ---------------- WRITE EVENT ----------------
      if (pkt.w_en && !pkt.full) begin
        exp_q.push_back(pkt.data_in);
        $display("SCOREBOARD: WRITE  data=0x%0h  depth=%0d",
                 pkt.data_in, exp_q.size());
      end

      // ---------------- READ EVENT -----------------
      else if (pkt.r_en && !pkt.empty) begin
        if (exp_q.size() == 0) begin
          $error("SCOREBOARD: READ when expected queue empty");
        end
        else begin
          exp_data = exp_q.pop_front();
          if (pkt.data_out !== exp_data) begin
            $error("SCOREBOARD MISMATCH: exp=0x%0h got=0x%0h",
                   exp_data, pkt.data_out);
          end
          else begin
            $display("SCOREBOARD: READ OK exp=0x%0h  depth=%0d",
                     pkt.data_out, exp_q.size());
          end
        end
      end

      // ignore anything else
    end
  endtask

endclass

