//---------------------------------------------------------
// Class: misty_monitor_pipe
//---------------------------------------------------------

// Base misty monitor

class axis_misty_monitor extends misty_monitor_base;

    `uvm_component_utils(axis_misty_monitor)

    //---------------------------------------------------------
    // Constructor
    //---------------------------------------------------------

    // Initializes the monitor component

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    logic [127:0] key;

    //---------------------------------------------------------
    // Task: get_data
    //---------------------------------------------------------

    // Captures data from the interface and sends it via the analysis port

    virtual task get_data();
        vif.wait_for_clks(1);
        if (vif.key_i [127:0] !== key) begin
          key=vif.key_i [127:0];
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
        end
    endtask 




endclass