//---------------------------------------------------------
// Class: misty_env_base
//---------------------------------------------------------

// Base misty environment

class misty_env_base extends uvm_env;

    `uvm_component_utils(misty_env_base)

    //---------------------------------------------------------
    // Constructor
    //---------------------------------------------------------

    // Initializes the environment component

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Components
    //---------------------------------------------------------

    misty_agent_base agent; 
    misty_top_scoreboard scb; 


    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------

    // This function is responsible for constructing the components and setting up the environment.
    
    virtual function void build_phase(uvm_phase phase);
        agent = misty_agent_base::type_id::create("agent", this);
        scb   = misty_top_scoreboard::type_id::create("scb", this);
    endfunction

    //---------------------------------------------------------
    // Function: connect_phase
    //---------------------------------------------------------

    // This function connects the monitor analysis port to the scoreboard's analysis import.

    virtual function void connect_phase(uvm_phase phase);
        if (agent == null || scb == null) begin
            `uvm_fatal("CONNECT", "Agents or scoreboard are null.")
        end
        if (agent.mon == null) begin
            `uvm_fatal("CONNECT", "Monitor in one of the agents is null.")
        end
        agent.mon.ap.connect(scb.imp_in);
    endfunction

endclass


//---------------------------------------------------------
// Class: misty_env_sc
//---------------------------------------------------------

//  environment for self check.

class misty_env_sc extends misty_env_base ;


    `uvm_component_utils(misty_env_sc)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    misty_scoreboard_sc scb_sc;

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        agent = misty_agent_base::type_id::create("agent", this);
        set_inst_override_by_type("agent.drv",
            misty_driver_base::get_type(), misty_rsp_driver::get_type());
        scb_sc   = misty_scoreboard_sc::type_id::create("scb", this);                    
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        if (agent == null || scb_sc == null) begin
            `uvm_fatal("CONNECT", "Agents or scoreboard are null.")
        end
        if (agent.mon == null) begin
            `uvm_fatal("CONNECT", "Monitor in one of the agents is null.")
        end
        agent.mon.ap.connect(scb_sc.imp_in);
    endfunction
    

endclass
