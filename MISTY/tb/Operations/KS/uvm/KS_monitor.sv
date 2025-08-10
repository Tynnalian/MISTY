//---------------------------------------------------------
// Class: KS_monitor_base
//---------------------------------------------------------

// Base KS monitor

class KS_monitor_base extends uvm_monitor;

    `uvm_component_utils(KS_monitor_base)


    virtual KS_intf vif;            
    typedef KS_seq_item_base REQ;   
    REQ req;                        
    uvm_analysis_port#(REQ) ap;       

    //---------------------------------------------------------
    // Constructor
    //---------------------------------------------------------

    // Initializes the monitor component

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

  


    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------

    // Sets up the virtual interface and analysis port

    virtual function void build_phase(uvm_phase phase);
        if (!uvm_resource_db#(virtual KS_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
                `uvm_fatal(get_name(), "Failed to get KS_intf");
        end
        ap = new("ap", this);   
    endfunction

    //---------------------------------------------------------
    // Task: reset_phase
    //---------------------------------------------------------

    // Handles reset behavior in the monitor

    virtual task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        vif.wait_for_reset();     
        vif.wait_for_unreset();    
        phase.drop_objection(this);
    endtask 

    //---------------------------------------------------------
    // Task: main_phase
    //---------------------------------------------------------

    // Main phase where the monitor actively collects data

    virtual task main_phase(uvm_phase phase);
        forever begin         
            get_data();            
        end
    endtask

    //---------------------------------------------------------
    // Task: get_data
    //---------------------------------------------------------

    // Captures data from the interface and sends it via the analysis port

    virtual task get_data();
        wait_for_valid_i();
        req = REQ::type_id::create("req");
        req.key = vif.key_i;
        wait_for_valid_o();
        req.expand_keys   = vif.expand_keys_o;
        `uvm_info(get_name(), $sformatf("Collected transaction: %s", 
            req.convert2string()), UVM_DEBUG);

        ap.write(req);
    endtask 

    virtual task wait_for_valid_i();
        do vif.wait_for_clks(1);
        while( !(vif.valid_i) );
    endtask

    virtual task wait_for_valid_o();
        do vif.wait_for_clks(1);
        while( !(vif.valid_o) );
    endtask

endclass


