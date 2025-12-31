class coverage;
    packet pkt;

    int wr_cnt;
    int rd_cnt;

    enum { WRITE, READ } state;
    enum { EMPTY, MID, FULL } depth;

covergroup fifo_cov;
    STATE_CP: coverpoint state;
    DEPTH_CP: coverpoint depth;

    cross STATE_CP, DEPTH_CP {
        illegal_bins WRITE_x_FULL =
            binsof(STATE_CP) intersect {WRITE} &&
            binsof(DEPTH_CP) intersect {FULL};

        illegal_bins READ_x_EMPTY =
            binsof(STATE_CP) intersect {READ} &&
            binsof(DEPTH_CP) intersect {EMPTY};
    }
endgroup

    function new();
        fifo_cov = new();
        wr_cnt = 0;
        rd_cnt = 0;
    endfunction

    task run();
        forever begin
            common::mon2scb.get(pkt);

            if (pkt.w_en == 1) begin
                state = WRITE;
                wr_cnt++;
            end
            else if (pkt.r_en == 1) begin
                state = READ;
                rd_cnt++;
            end
            else begin
                continue; 
            end

            if (pkt.full == 1)
                depth = FULL;
            else if (pkt.empty == 1)
                depth = EMPTY;
            else
                depth = MID;

            fifo_cov.sample();

            $display("COV: state=%s depth=%s wr=%0d rd=%0d",
                     state.name(), depth.name(), wr_cnt, rd_cnt);
        end
    endtask
endclass

