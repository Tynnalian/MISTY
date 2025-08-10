//---------------------------------------------------------
// Class: misty_monitor_pipe
//---------------------------------------------------------

// Base misty monitor

class misty_monitor_pipe extends misty_monitor_base;

    `uvm_component_utils(misty_monitor_pipe)

    //---------------------------------------------------------
    // Constructor
    //---------------------------------------------------------

    // Initializes the monitor component

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction



     //---------------------------------------------------------
    // Task: get_data
    //---------------------------------------------------------

    // Captures data from the interface and sends it via the analysis port

    virtual task get_data();
        do vif.wait_for_clks(1);
        while( !((vif.valid_i || vif.valid_o) && !vif.stall_i));
        req = REQ::type_id::create("req");
        req.valid_i = vif.valid_i;
        req.valid_o = vif.valid_o;
        req.text_i = vif.text_i;
        req.key = vif.key_i;
        req.enc = vif.enc_i;
        req.text_o   = vif.text_o;
        `uvm_info(get_name(), $sformatf("Collected transaction: %s", 
            req.convert2string()), UVM_DEBUG);
        ap.write(req);
    endtask 




endclass

//---------------------------------------------------------
// Class: misty_monitor_pipe_sc
//---------------------------------------------------------

//  misty monitor for pipe self_check

class misty_monitor_pipe_sc extends misty_monitor_base;

    `uvm_component_utils(misty_monitor_pipe_sc)

    //---------------------------------------------------------
    // Constructor
    //---------------------------------------------------------

    // Initializes the monitor component

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual task wait_for_handshake();
        do vif.wait_for_clks(1);
        while( !(vif.valid_i) );
    endtask






endclass
