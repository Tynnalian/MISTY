//---------------------------------------------------------
// Class: KS_agent_base
//---------------------------------------------------------

// Base agent

class KS_agent_base extends uvm_agent;

    `uvm_component_utils(KS_agent_base)

    uvm_sequencer # (KS_seq_item_base) seqr;
    KS_driver_base   drv;
    KS_monitor_base  mon;

    //---------------------------------------------------------
    // Function: new
    //---------------------------------------------------------
    
    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------
    
    virtual function void build_phase(uvm_phase phase);
        create_components();
    endfunction

    //---------------------------------------------------------
    // Function: create_components 
    //---------------------------------------------------------
    
    virtual function void create_components();
            drv   = KS_driver_base::type_id::create("drv", this);
            seqr  = uvm_sequencer#(KS_seq_item_base)::type_id::create("seqr", this);
            mon = KS_monitor_base::type_id::create("mon", this);
    endfunction

    //---------------------------------------------------------
    // Function: connect_phase 
    //---------------------------------------------------------

    virtual function void connect_phase(uvm_phase phase);
            drv.seq_item_port.connect(seqr.seq_item_export); 
    endfunction
    

endclass

