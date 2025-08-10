//---------------------------------------------------------
// Class: misty_driver_base
//---------------------------------------------------------

// misty driver.

class misty_driver_base extends uvm_driver#(misty_seq_item_base);

    // For every UVM component you must write this line.

    `uvm_component_utils(misty_driver_base)

    
    // Always driver has virtual interface as custom field.
    
    virtual misty_intf vif;

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        if(!uvm_resource_db#(virtual misty_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
            `uvm_fatal(get_name(), "Can't get misty_intf!");
        end
    endfunction

    // Reset phase.

    virtual task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        vif.wait_for_reset();
        reset();
        vif.wait_for_unreset();
        phase.drop_objection(this);
    endtask

    // Main phase.

    virtual task main_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            do_delay();
             set_data();
            do vif.wait_for_clks(1);
            while(!(vif.ready_o));
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
        vif.stall_i   <=  1'b0;        
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
// Class: misty_rsp_driver
//---------------------------------------------------------

// misty driver with response transaction

class misty_rsp_driver extends misty_driver_base;

    `uvm_component_utils(misty_rsp_driver)

    // Constructor.
    
    misty_seq_item_base resp;

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        if(!uvm_resource_db#(virtual misty_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
            `uvm_fatal(get_name(), "Can't get misty_intf!");
        end
 //       resp = misty_seq_item_base::type_id::create("resp");
    endfunction

    virtual task main_phase(uvm_phase phase); 
       // misty_seq_item_base resp = misty_seq_item_base::type_id::create("resp");
        forever begin
            seq_item_port.get_next_item(req);
            do_delay();
            drive_data(req,resp);
            resp.set_id_info(req);
            // unset_data();
            seq_item_port.item_done(resp);
        end
    endtask

    virtual task drive_data(misty_seq_item_base req, output misty_seq_item_base rsp );
        misty_seq_item_base resp;
        if(!$cast(resp,req.clone())) `uvm_fatal("DRVI", "cast to resp failed") 
        vif.valid_i <= 1'b1;
        vif.text_i  <= req.text_i;
        vif.key_i   <= req.key;
        vif.enc_i   <= req.enc;
        vif.wait_for_clks(1);
        resp.text_i <= vif.text_i;
        resp.key    <= vif.key_i;
        resp.enc    <= vif.enc_i;
        unset_data();
        do vif.wait_for_clks(1);
        while(!(vif.valid_o));
        resp.text_o <= vif.text_o;
        rsp = resp;
    endtask




endclass

