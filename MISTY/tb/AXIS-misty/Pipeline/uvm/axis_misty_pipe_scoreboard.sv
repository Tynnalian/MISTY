//---------------------------------------------------------
// Class: axis_misty_pipe_scoreboard
//---------------------------------------------------------

class axis_misty_pipe_scoreboard extends axis_misty_scoreboard;
    
    `uvm_component_utils(axis_misty_pipe_scoreboard)
    

    int tr_cnt;

    int check_cnt;

    mailbox #(axis_item_t) axis_in, axis_out;
   

    misty_seq_item_base t_in;

    time time_out;
    axis_item_t bypass_tmp;
    


    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
        t_in = misty_seq_item_base::type_id::create("t_in");
    endfunction
    

    virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            axis_in = new();
            axis_out = new();
    endfunction
    

    virtual function void write_axis_in(mvc_sequence_item_base t);
        axis_item_t t_in;
        $cast(t_in, t.clone());
        `uvm_info(get_name(), $sformatf("Got item: %s",
            t_in.convert2string()), UVM_DEBUG);
        // marker show that it's in transaction    
        // t_in.data [194] = 1'b1;
        if(!this.axis_in.try_put(t_in)) $fatal("CANT put in tran");
        //  else $info("!!!! IN tran %d",t_in.data [194]);
    endfunction

    virtual function void write_axis_out(mvc_sequence_item_base t);
        axis_item_t t_in;
        $cast(t_in, t.clone());
        `uvm_info(get_name(), $sformatf("Got item: %s",
            t_in.convert2string()), UVM_DEBUG);   
        this.axis_out.try_put(t_in);
    endfunction

    virtual task main_phase(uvm_phase phase);
        bit enable;
        int time_in,time_out;
        axis_item_t axis_t; 
        fork
         forever  begin
          // axis_sort.get(axis_t);
          sort_axis_tran();
         end
         forever check_axis_tran();
        //  forever check_bypass_tran();
        join
    endtask

    virtual task check_axis_tran();
      axis_item_t axis_tmp;
      axis_mbx_in.get(axis_tmp);
      t_in.text_i = get_data(axis_tmp);
      t_in.key = get_key(axis_tmp);
      t_in.enc    = get_enc(axis_tmp);
      axis_mbx_out.get(axis_tmp);
      t_in.text_o = get_data(axis_tmp);  
      `uvm_info(get_name(), $sformatf("Got item: %s",
      t_in.convert2string()), UVM_DEBUG);           
      cov_wrapper.sample(t_in);
      check_cnt++;
      // $display("TRANSACTION CHECK %d",check_cnt);
      do_check(t_in);
    endtask

    // virtual task check_bypass_tran();
    //   axis_item_t axis_in,axis_out;
    //   by_pass_in.get(axis_in);
    //   by_pass_out.get(axis_out);
    //   if (!(check_bypass(axis_in,axis_out))) begin
    //       $error("Bypass check failed EXPECTED: %h REAL %h",get_data(axis_in),get_data(axis_out));
    //       `uvm_error({get_name(),": BAD"}, $sformatf(
    //                     {"Bypass check failed EXPECTED: %h, ",
    //                    "REAL %h"},get_data(axis_in), get_data(axis_out) ));
    //   end  
    // endtask


    virtual task sort_axis_tran();
      axis_item_t axis_i,axis_o;
      axis_in.get(axis_i);
      $info("check");
      if (its_passby_tr(axis_i)) begin
        if (axis_i.get_end_time() >= time_out) begin
            axis_out.get(axis_o);
            check_bypass(axis_i,axis_o);            
          end
      end    
      else begin
        axis_out.get(axis_o);
        time_out=axis_o.get_begin_time();
        axis_mbx_in.put(axis_i);
        axis_mbx_out.put(axis_o);
      end           
    endtask

    //  virtual task sort_axis_tran();
    //   axis_item_t axis_tmp,axis_o;
    //   axis_sort.get(axis_tmp);
    //   $info("TRAN TO SORT %h",axis_tmp.data [191:64]);
    //   if (its_in(axis_tmp)) begin
    //     if(its_passby_tr(axis_tmp)) begin 
    //       if (tr_cnt == 0) begin
    //         if (wait_by_pass) by_pass_cnt ++;
    //         $display("by_pass_cnt %d",by_pass_cnt);  
    //         $info("by pass %h",get_data(axis_tmp));
    //         wait_by_pass = 1;
    //         axis_by_pass = axis_tmp;
    //         by_pass_in.put(axis_tmp);
    //       end 
    //       else if (tr_cnt == 1) begin
    //       axis_by_pass = axis_tmp;
    //       bypass_1 = 1;
    //        $info("!!!!!!!!!!BY PASS 1!!!!!!!!!!!!");
    //       end
    //       else $info("SKIP tran");     
    //     end
    //     else begin
    //       $info("in tran %h",get_key(axis_tmp));
    //       axis_mbx_in.put(axis_tmp);
    //       tr_cnt++;
    //       $info("tran_cnt in %h",tr_cnt);  
    //     end  
    //   end
    //   else begin
    //       // $info("OUT TRAN %h",axis_tmp.data [191:64]);
    //       if (wait_by_pass) begin
    //         $info("CHECK BY PASS");
    //           if (axis_tmp.get_end_time ()==axis_by_pass.get_end_time ()) begin
    //               axis_mbx_out.put(axis_tmp);
    //               tr_cnt--;
    //             end 
    //           by_pass_out.put(axis_tmp);
              
    //           if (by_pass_cnt > 2) begin 
    //             wait_by_pass = 1;
    //             // by_pass_cnt=0;
    //           end
    //           else wait_by_pass = 0;
    //        end      
    //       else if (bypass_1) begin
    //         $info("bypass1_out");
    //         if (axis_tmp.get_end_time ()==axis_by_pass.get_end_time ()) begin
    //           axis_mbx_out.put(axis_tmp);
    //           tr_cnt--;
    //           check_bypass_when_cnt_1 = 1;
    //           $info("BYpass check when 1");
    //         end
    //         else if (check_bypass_when_cnt_1) begin
    //           if (!(check_bypass(axis_tmp,axis_by_pass))) begin
    //                  $error("Bypass check failed EXPECTED: %h REAL %h",get_data(axis_by_pass),get_data(axis_tmp));
    //                  `uvm_error({get_name(),": BAD"}, $sformatf(
    //                        {"Bypass check failed EXPECTED: %h, ",
    //                        "REAL %h"},get_data(axis_by_pass), get_data(axis_tmp) ));
    //           end
    //           bypass_1 = 0;
    //           check_bypass_when_cnt_1=0;
    //           wait_by_pass = 0;
    //           $display("BYPASS CHECK");
    //         end
    //         else begin 
    //           bypass_1 = 0;
    //           axis_mbx_out.put(axis_tmp);
    //           tr_cnt--;
    //           $info("tran_cnt out %h",tr_cnt);
    //         end   
    //       end    
    //       else begin
    //         axis_mbx_out.put(axis_tmp);
    //         tr_cnt--;
    //         $info("tran_cnt out %h",tr_cnt);
    //       end
    //   end   
    // endtask


    virtual function bit its_in(axis_item_t axis_tr);
      return axis_tr.data[194];
    endfunction

    virtual function bit its_passby_tr(axis_item_t axis_tr);
      return !axis_tr.data[193];
    endfunction 

    virtual function bit [63:0] get_data(axis_item_t axis_tr);
      return axis_tr.data[63:0];
    endfunction

    virtual function bit [127:0] get_key(axis_item_t axis_tr);
      return axis_tr.data[191:64];
    endfunction

    virtual function bit  get_enc(axis_item_t axis_tr);
      return axis_tr.data[192];
    endfunction

    virtual function bit check_bypass (axis_item_t axis_tr_i,
    axis_item_t axis_tr_o);
      logic data_i = get_data(axis_tr_i);
      logic data_o = get_data(axis_tr_o);
      return (data_i === data_o );
    endfunction



      virtual task reset_phase(uvm_phase phase);
        axis_item_t axis_tmp;
        super.reset_phase( phase );
        while(axis_in.try_get(axis_tmp));
        while(axis_out.try_get(axis_tmp));
        time_out = 0;
    endtask

endclass