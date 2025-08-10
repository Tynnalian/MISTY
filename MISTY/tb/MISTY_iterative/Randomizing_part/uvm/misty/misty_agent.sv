//---------------------------------------------------------
// Class: misty_agent
//---------------------------------------------------------

// misty agent.

class misty_agent_base extends uvm_agent;


    `uvm_component_utils(misty_agent_base)

    // Driver and sequencer. For this example monitor
    // is not used.

    misty_driver_base drv;
    uvm_sequencer#(misty_seq_item_base)  seqr;
    misty_monitor_base mon;

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        create_components();
    endfunction

    // Creating components.

    virtual function void create_components();
        drv  = misty_driver_base::type_id::create("drv", this);
        mon  = misty_monitor_base::type_id::create("mon", this);
        seqr = uvm_sequencer#(misty_seq_item_base)::type_id::create("seqr", this);
    endfunction

    // Connect phase.

    virtual function void connect_phase(uvm_phase phase);
        drv.seq_item_port.connect(seqr.seq_item_export);
    endfunction

endclass
