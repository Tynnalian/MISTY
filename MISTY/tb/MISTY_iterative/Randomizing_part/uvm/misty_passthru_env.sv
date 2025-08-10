//---------------------------------------------------------
// Class: misty_passthru_env_base
//---------------------------------------------------------

// misty passthrough environment.

class misty_passthru_env_base extends KS_env_base ;


    `uvm_component_utils(misty_passthru_env_base)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    //---------------------------------------------------------
    // Field: Component
    //---------------------------------------------------------
    
    //  misty agent


    misty_agent_base misty_agent;

    misty_scoreboard_base scb;

    // Passthrough sequence handle.
    
    misty_passthru_seq passthru_seq;

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        // Create passthrough sequence and pass it to the resource database.
        passthru_seq = misty_passthru_seq::type_id::create("passthru_seq");
        uvm_resource_db#(misty_passthru_seq)::set(
           {get_full_name(), ".agent.drv"}, "passthru_seq", passthru_seq, this
        );
        agent      =  KS_agent_base::type_id::create("agent",  this);
        misty_agent = misty_agent_base::type_id::create("misty_agent", this);
        set_inst_override_by_type("agent.drv",
            KS_driver_base::get_type(), KS_passthru_driver_base::get_type());
        set_inst_override_by_type("agent.mon",
            KS_monitor_base::get_type(), KS_monitor_empty::get_type());    
        scb   = misty_scoreboard_base::type_id::create("scb", this);    
    endfunction

    // Connect phase.

    virtual task main_phase(uvm_phase phase);
        // Start passthrough sequence on high level
        // passthrough driver.
        passthru_seq.start(misty_agent.seqr);
    endtask
    

        // This function connects the monitor analysis port to the scoreboard's analysis import.

    virtual function void connect_phase(uvm_phase phase);
        if (misty_agent == null || scb == null) begin
            `uvm_fatal("CONNECT", "Agents or scoreboard are null.")
        end
        if (misty_agent.mon == null) begin
            `uvm_fatal("CONNECT", "Monitor in one of the agents is null.")
        end
        misty_agent.mon.ap.connect(scb.imp_in);
    endfunction


endclass

//---------------------------------------------------------
// Class: misty_passthru_env_sc
//---------------------------------------------------------

//  environment for sc.

class misty_passthru_env_sc extends misty_passthru_env_base ;


    `uvm_component_utils(misty_passthru_env_sc)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        // Create passthrough sequence and pass it to the resource database.
        uvm_factory factory=uvm_factory::get();
        set_inst_override_by_type("scb",
            misty_scoreboard_base::get_type(), misty_scoreboard_sc::get_type()); 
        set_type_override_by_type(misty_passthru_seq::get_type(), misty_passthru_seq_sc::get_type());
        set_inst_override_by_type("misty_agent.drv",
            misty_driver_base::get_type(), misty_rsp_driver::get_type()); 
        super.build_phase(phase);
        factory.print();         
    endfunction

endclass