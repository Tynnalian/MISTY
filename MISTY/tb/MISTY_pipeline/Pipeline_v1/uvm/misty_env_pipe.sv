//---------------------------------------------------------
// Class: misty_env_pipe
//---------------------------------------------------------

//  environment for pipeline.

class misty_env_pipe extends misty_env_base ;


    `uvm_component_utils(misty_env_pipe)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    misty_scoreboard_pipe scb_pipe;

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        uvm_factory factory = uvm_factory::get();
        set_inst_override_by_type("scb",
            misty_top_scoreboard::get_type(), misty_scoreboard_pipe::get_type()); 
        super.build_phase(phase);
        set_inst_override_by_type("agent.drv",
            misty_driver_base::get_type(), misty_driver_pipe::get_type());
        set_inst_override_by_type("agent.mon",
            misty_monitor_base::get_type(), misty_monitor_pipe::get_type());
        factory.print();                                    
    endfunction

endclass

//---------------------------------------------------------
// Class: misty_env_sc
//---------------------------------------------------------

//  environment for sc.

class misty_env_pipe_sc extends misty_env_base ;


    `uvm_component_utils(misty_env_pipe_sc)

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
        set_inst_override_by_type("agent.mon",
            misty_monitor_base::get_type(), misty_monitor_pipe_sc::get_type());            
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