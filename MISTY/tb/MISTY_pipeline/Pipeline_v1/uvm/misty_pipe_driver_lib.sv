//---------------------------------------------------------
// Class: misty_driver_pipe
//---------------------------------------------------------

// misty driver.

class misty_driver_pipe extends misty_driver_base;

    // For every UVM component you must write this line.

    `uvm_component_utils(misty_driver_pipe)

    
  

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction



    // Main phase.

    virtual task main_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            do_delay();
            set_data();
            vif.wait_for_clks(1);
            unset_data();
            seq_item_port.item_done();
        end
    endtask

    // Tasks above do high-level routines

    virtual task reset();
        vif.valid_i <=  1'b0;
        vif.text_i  <=  64'b0;
        vif.key_i   <=  256'b0;
        vif.enc_i   <=  1'b0;
        vif.stall_i  <= 1'b0;

    endtask

    virtual task set_data();
        vif.valid_i <= 1'b1;
        vif.text_i  <= req.text_i;
        vif.key_i   <= req.key;
        vif.enc_i   <= req.enc;
    endtask

    virtual task unset_data();
        reset();
    endtask

    virtual task do_delay();
        vif.wait_for_clks($urandom_range(0, 10));
    endtask

endclass


//---------------------------------------------------------
// Class: misty_driver_pipe_stall
//---------------------------------------------------------

// misty driver with stall while encryption.

class misty_driver_pipe_stall extends misty_driver_pipe;

    // For every UVM component you must write this line.

    `uvm_component_utils(misty_driver_pipe_stall)

    
  

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction



    // Main phase.

    virtual task main_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            do_delay();
            set_data();
            do_delay();
            vif.stall_i <= 1'b1;
            vif.wait_for_clks(1);
            unset_data();
            seq_item_port.item_done();
        end
    endtask

  // do_delay in time 0:34 because it's time of computing
    virtual task do_delay();
        vif.wait_for_clks($urandom_range(0, 34));
    endtask

endclass

//---------------------------------------------------------
// Class: misty_driver_valid_stall
//---------------------------------------------------------

// driver that set valid in high level while stall.

class misty_driver_valid_stall extends misty_driver_pipe;

    // For every UVM component you must write this line.

    `uvm_component_utils(misty_driver_valid_stall)

    
  

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction



    // Main phase.

    virtual task main_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            set_data();
            vif.wait_for_clks(1);
            vif.valid_i <=0;
            do_delay();
            vif.stall_i <= 1'b1;
            how_much_valids($urandom_range(0, 15));
            unset_data();
            seq_item_port.item_done();
        end
    endtask

    virtual task do_delay();
        vif.wait_for_clks(2);
    endtask

    virtual task how_much_valids(int iters);
        for (int i = 0; i < iters; i++) begin
            vif.valid_i <=1;
            vif.wait_for_clks(1);
        end    
    endtask



endclass


