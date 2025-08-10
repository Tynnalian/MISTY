//---------------------------------------------------------
// Class: misty_env_axis
//---------------------------------------------------------

//  misty environment for axis-verison

class axis_misty_env extends misty_env_base;

    `uvm_component_utils(axis_misty_env)

   // AXI-Stream VIP agents.
  
    axis_agent_t ag_master;
    axis_agent_t ag_slave;

    // axis_mistty_scoreboard
     axis_misty_scoreboard scb_axis;


    //---------------------------------------------------------
    // Constructor
    //---------------------------------------------------------

    // Initializes the environment component

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------

    // This function is responsible for constructing the components and setting up the environment.
    
    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("scb",
            misty_top_scoreboard::get_type(), axis_misty_scoreboard::get_type());
        super.build_phase(phase);
        set_inst_override_by_type("agent.drv",
            misty_driver_base::get_type(), misty_driver_axis::get_type());
        set_inst_override_by_type("agent.mon",
            misty_monitor_base::get_type(), axis_misty_monitor::get_type());
        ag_master = axis_agent_t::type_id::create("ag_master", this);
        ag_slave = axis_agent_t::type_id::create("ag_slave", this);
        // Get configs to agents.
        if(!uvm_config_db #(axis_config_t)::get(
            this, "", "ag_master_cfg" , ag_master.cfg)) begin
            `uvm_error(get_full_name(), "Can't get 'ag_master_cfg'");
        end
        if(!uvm_config_db #(axis_config_t)::get(
            this, "", "ag_slave_cfg" , ag_slave.cfg)) begin
            `uvm_error(get_full_name(), "Can't get 'ag_slave_cfg'");
        end
    endfunction

     // End of elaboration phase.

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        // Set verbosity for sequencers to suppress
        // some sequence start info.
        ag_master.m_sequencer.set_report_verbosity_level(UVM_LOW);
        ag_slave.m_sequencer.set_report_verbosity_level(UVM_LOW);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        $cast(scb_axis,scb);
        if (agent == null || scb_axis == null) begin
            `uvm_fatal("CONNECT", "Agents or scoreboard are null.")
        end
        if (agent.mon == null) begin
            `uvm_fatal("CONNECT", "Monitor in one of the agents is null.")
        end
        agent.mon.ap.connect(scb_axis.imp_in);      
        ag_master.ap["transfer_ap"].connect(scb_axis.axis_imp_in);
        ag_slave.ap["transfer_ap"].connect(scb_axis.axis_imp_out);
    endfunction




endclass