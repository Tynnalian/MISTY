//---------------------------------------------------------
// Class: axis_misty_test_base
//---------------------------------------------------------

// AXI-Stream misty test.

class axis_misty_test_base extends uvm_test;

    // For every UVM component you must write this line.

    `uvm_component_utils(axis_misty_test_base)

    // Environment.

    axis_misty_env env;

    //RESET_AGENT
    reset_agent     ag;
    reset_agent_cfg cfg; 

    // Agent configurations.

    axis_config_t ag_master_cfg;
    axis_config_t ag_slave_cfg;

    virtual misty_intf vif;

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        uvm_resource_db#(int)::set(
           "*", "item_amount", 1, this
        );
        uvm_resource_db#(int)::set(
           "*", "write_delay_max", 1, this
        );
        uvm_resource_db#(int)::set(
           "*", "write_delay_min", 0, this
        );
        if(!uvm_resource_db#(virtual misty_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
            `uvm_fatal(get_name(), "Can't get misty_intf!");
        end
        cfg = reset_agent_cfg::type_id::create("cfg");
        randomize_cfg();
        uvm_resource_db#(reset_agent_cfg)::set(
            {get_full_name(), ".*"}, "cfg", cfg);
        ag = reset_agent::type_id::create("ag", this);
        // Create environment.
        env = axis_misty_env::type_id::create("env", this);
        // Create agents configurations.
        ag_master_cfg = axis_config_t::type_id::create("ag_master_cfg");
        ag_slave_cfg  = axis_config_t::type_id::create("ag_slave_cfg");

        // Setup agents configurations.
        setup_configs();
        // Pass configurations to the resource database.
        pass_configs();
    endfunction

    // Function fot defining configuration settings.

    virtual function void setup_configs();
        // Get AXI-Stream interfaces to configurations.
        if(!uvm_config_db #(axis_if_t)::get(
            this, "", "AXI4STREAM_MASTER" , ag_master_cfg.m_bfm)) begin
            `uvm_error(get_full_name(), "Can't get 'AXI4STREAM_MASTER'");
        end
        if(!uvm_config_db #(axis_if_t)::get(
            this, "", "AXI4STREAM_SLAVE" , ag_slave_cfg.m_bfm)) begin
            `uvm_error(get_full_name(), "Can't get 'AXI4STREAM_SLAVE'");
        end
        // Set agent type to master.
        ag_master_cfg.agent_cfg.agent_type = AXI4STREAM_MASTER;
        // Enable and setup coverage.
        ag_master_cfg.agent_cfg.en_cvg = 1;
        ag_master_cfg.m_coverage_per_instance = 1;
        ag_master_cfg.set_coverage_instance_name("cov");
        // Disable user data for master.
        ag_master_cfg.m_bfm.config_enable_user_data = 0;
        ag_master_cfg.m_bfm.config_enable_strb = 0;
        ag_master_cfg.m_bfm.config_max_latency_TVALID_assertion_to_TREADY=DURATION;
        // Set agent type to slave.
        ag_slave_cfg.agent_cfg.agent_type = AXI4STREAM_SLAVE;
        //disable automatic start of slave sequence
        ag_slave_cfg.agent_cfg.en_slv_seq = 0; 
        // Setup ready delays.
        ag_slave_cfg.m_min_ready = 10;
        ag_slave_cfg.m_max_ready = 20;
        // Disable user data for slave.
        ag_slave_cfg.m_bfm.config_enable_user_data = 0;




        // Disable some SVA for slave as TLAST, TKEEP and TSTRB
        // are not supported.
        ag_slave_cfg.m_bfm.config_enable_assertion[AXI4STREAM_TSTRB_Z] = 0;
        ag_slave_cfg.m_bfm.config_enable_assertion[AXI4STREAM_TKEEP_Z] = 0;
        ag_slave_cfg.m_bfm.config_enable_assertion[AXI4STREAM_TLAST_Z] = 0;
    endfunction

    // Function for passing configurations to the resource database.

    virtual function void pass_configs();
        uvm_config_db #(axis_config_t)::set(
            this, "env", "ag_master_cfg" , ag_master_cfg);
        uvm_config_db #(axis_config_t)::set(
            this, "env", "ag_slave_cfg" , ag_slave_cfg);
    endfunction


    //---------------------------------------------------------
    // Function: randomize_cfg
    //---------------------------------------------------------
    
    // Agent configuration randomization.

    virtual function void randomize_cfg();
        if(!cfg.randomize()) begin
            `uvm_fatal(get_name(), "Can't randomize 'cfg'!");
        end
    endfunction

    // Run phase.

    virtual task main_phase(uvm_phase phase);
        // Create and start sequence on master.
        misty_seq_base seq;
        axis_misty_seq_base misty_seq;
        slave_seq_t  slave;
        phase.raise_objection(this);
        slave = slave_seq_t::type_id::create("slave");
        fork
        slave.start(env.ag_slave.m_sequencer);
        begin 
         repeat(8) begin
           misty_seq = axis_misty_seq_base::type_id::create("misty_seq");
           seq = misty_seq_base::type_id::create("seq");
           misty_seq.set_sequencer(env.ag_master.m_sequencer);

           misty_seq.inter_xfer_dly = $urandom_range(5, 10);
           if(!misty_seq.randomize()) begin
              `uvm_fatal(get_full_name(), "Can't randomize sequence!");
           end 
           seq.start(env.agent.seqr);
    
           misty_seq.start(env.ag_master.m_sequencer);
         
          //wait for last transaction encrypted
           vif.wait_for_clks(DURATION);
          end
        end
        join_any
        phase.drop_objection(this);
    endtask

    virtual task reset_phase(uvm_phase phase);
        reset_seq seq;
        phase.raise_objection(this);
        seq = reset_seq::type_id::create("seq");
        seq.start(ag.sqr);
        phase.drop_objection(this);
    endtask


endclass


//---------------------------------------------------------
// Class: axis_misty_test_reset
//---------------------------------------------------------

// axis_misty_test with 5 reset in a row.

class axis_misty_test_reset extends axis_misty_test_base;


    `uvm_component_utils(axis_misty_test_reset)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.
    int reset_cnt = 0;

 

    virtual function void randomize_cfg();
        if(!cfg.randomize() with {
            sync_type     == SYNC_BOTH;
            sync_edge     == NEGEDGE;
        }) begin
            `uvm_fatal(get_name(), "Can't randomize 'cfg'!");
        end
    endfunction


    virtual task main_phase(uvm_phase phase);
        phase.raise_objection( this );
        fork
        super.main_phase( phase );
        join_none
        if (reset_cnt <= 5) begin
           if (reset_cnt == 0) begin 
               env.agent.drv.vif.wait_for_clks(3000);
               reset_cnt ++;   
           end 
           else begin
               env.agent.drv.vif.wait_for_clks($urandom_range(500,1000));
               reset_cnt ++;        
           end
        // finish_seq
            env.agent.seqr.stop_sequences();
            env.ag_master.m_sequencer.stop_sequences();
            env.ag_slave.m_sequencer.stop_sequences();
        // go to reset
            phase.jump(uvm_pre_reset_phase::get());
        end
        phase.drop_objection( this );

    endtask

endclass    
