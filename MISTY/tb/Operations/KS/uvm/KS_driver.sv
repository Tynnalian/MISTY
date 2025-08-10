//---------------------------------------------------------
// Class: KS_driver_base
//---------------------------------------------------------

// base KS driver

class KS_driver_base extends uvm_driver#(KS_seq_item_base);

    `uvm_component_utils(KS_driver_base) 
    

    virtual KS_intf vif;      
    int write_delay_min;   
    int write_delay_max;   
   

    //---------------------------------------------------------
    // Function: new
    //---------------------------------------------------------

    // Constructor for the KS driver.
 
    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Task: reset
    //---------------------------------------------------------

    // Task to reset the KS signals to their default state.

    virtual task reset();
        vif.valid_i   <= 0;
        vif.key_i     <= 0;
        
    endtask 

    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------
    // Build phase is used to read conKSguration parameters
    // from the UVM resource database and set up the interface.

    virtual function void build_phase(uvm_phase phase);
        if (!uvm_resource_db#(virtual KS_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
            `uvm_fatal(get_name(), "Can't get KS_intf!");
        end else $display(vif);

        if (!uvm_resource_db#(int)::read_by_name("env.agent.drv", "write_delay_max", write_delay_max))
            `uvm_error(get_name(), "Can't get write_delay_max");
        if (!uvm_resource_db#(int)::read_by_name("env.agent.drv", "write_delay_min", write_delay_min))
            `uvm_error(get_name(), "Can't get write_delay_min");



    endfunction

    //---------------------------------------------------------
    // Task: pre_reset_phase
    //---------------------------------------------------------

    // Waits for the reset signal before taking any actions.

    virtual task pre_reset_phase(uvm_phase phase);
        vif.wait_for_reset();
    endtask

    //---------------------------------------------------------
    // Task: reset_phase
    //---------------------------------------------------------

    // Handles reset functionality during the reset phase.
    
    virtual task reset_phase(uvm_phase phase);
        phase.raise_objection(this);
        vif.wait_for_reset();
        reset();
        vif.wait_for_unreset();
        phase.drop_objection(this);
    endtask  


virtual task main_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            set_data();
            do vif.wait_for_clks(1);
            while(!(vif.valid_o));
            unset_data();
            seq_item_port.item_done();
        end
    endtask

    // Tasks above do high-level routines

    virtual task set_data();
        vif.wait_for_clks($urandom_range(write_delay_min,write_delay_max));
        vif.valid_i   <= 'b1;
        vif.key_i      <= req.key;
        vif.wait_for_clks(1);
        vif.valid_i   <= 'b0;  
    endtask


    //---------------------------------------------------------
    // Task: unset_data
    //---------------------------------------------------------

    // Resets KS signals to their default state.

    virtual task unset_data();
        reset();
    endtask 

endclass