//---------------------------------------------------------
// Class: FO_env_base
//---------------------------------------------------------

// Base FO environment

class FO_env_base extends uvm_env;

    `uvm_component_utils(FO_env_base)

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

    FO_agent_base agent; 
    FO_scoreboard_base scb; 


    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------

    // This function is responsible for constructing the components and setting up the environment.
    
    virtual function void build_phase(uvm_phase phase);

        agent = FO_agent_base::type_id::create("agent", this);
        scb   = FO_scoreboard_base::type_id::create("scb", this);
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
