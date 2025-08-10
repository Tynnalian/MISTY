//---------------------------------------------------------
// Class: axi4lite_loopback_env
//---------------------------------------------------------

// Environment for AXI4-Lite VIP loopback.

class axi4lite_misty_env extends uvm_env;

    `uvm_component_utils(axi4lite_misty_env)
    `uvm_component_new


    //---------------------------------------------------------
    // Fields
    //---------------------------------------------------------

    // AXI4 master configuration, delay database and agent.

    axi4_config_t       axi4_master_config;
    axi4_master_delay_t axi4_master_delay;
    axi4_agent_t        axi4_master;

    // AXI4 slave configuration, delay database and agent.

    axi4_config_t      axi4_slave_config;
    axi4_slave_delay_t axi4_slave_delay;
    axi4_agent_t       axi4_slave;

    // MISTY_AGENT

    misty_agent_base misty_agent;

    // MISTY_AXI4_scrb

    misty_axil_scoreboard_base scrb;

    //---------------------------------------------------------
    // Field: GPIO_Agent with config.
    //---------------------------------------------------------

    gpio_agent     enc_ag;
    gpio_agent     dec_ag;


    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------
    
    // Create environment, configure it

    virtual function void build_phase(uvm_phase phase);
        
        // create scoreboard 
        scrb = misty_axil_scoreboard_base::type_id::create("scrb",this);

        // Apply overrides.
        apply_overrides();

        // Create master and slave agents.
        create_agents();
        
        // Create configurations.
        create_configs();

        // Set AXI4 common settings.
        set_common();

        // Set AXI4 address map.
        set_addr_map();

        // Set AXI4 master basic settings.
        set_master_basic();

        // Set AXI4 master delays.
        set_master_delay();

        // Set AXI4 slave basic settings.
        set_slave_basic();

        // Set AXI4 slave delays.
        set_slave_delay();

    endfunction


    //---------------------------------------------------------
    // Function: apply_overrides
    //---------------------------------------------------------
    
    // Apply all needed components/objects overrides.

    virtual function void apply_overrides();
        set_inst_override_by_type("misty_agent.drv",
            misty_driver_base::get_type(), misty_driver_axis::get_type());
        set_inst_override_by_type("misty_agent.mon",
            misty_monitor_base::get_type(), axis_misty_monitor::get_type());
    endfunction


    //---------------------------------------------------------
    // Function: create_agents
    //---------------------------------------------------------
    
    // Create agents.

    virtual function void create_agents();
        axi4_master = axi4_agent_t::type_id::create(
            "axi4_master", this);
        axi4_slave  = axi4_agent_t::type_id::create(
            "axi4_slave",  this);
        misty_agent = misty_agent_base::type_id::create(
            "misty_agent",this);
        enc_ag = gpio_agent::type_id::create(
            "enc_ag",this);
        dec_ag = gpio_agent::type_id::create(
            "dec_ag",this);
    endfunction


    //---------------------------------------------------------
    // Function: create_configs
    //---------------------------------------------------------
    
    // Create agents configurations.

    virtual function void create_configs();
        axi4_master_config = axi4_config_t::type_id::create(
                "axi4_master_config", this);
        axi4_slave_config  = axi4_config_t::type_id::create(
                "axi4_slave_config", this);
    endfunction


    //---------------------------------------------------------
    // Function: set_common
    //---------------------------------------------------------
    
    // Configure setting common for master and slave.

    virtual function void set_common();

        // Set AXI4-Lite.
        axi4_master_config.agent_cfg.if_type = AXI4_LITE;
        axi4_slave_config.agent_cfg.if_type = AXI4_LITE;

        // Pass configurations to AXI4 agents.
        axi4_master.cfg = axi4_master_config;
        axi4_slave.cfg  = axi4_slave_config;

        // Obtain interfaces.
        begin
            string intf_name = "AXI4_MASTER_IF";
            if(!uvm_resource_db #( axi4_bfm_type )::read_by_name( get_full_name(),
                intf_name, axi4_master_config.m_bfm )) `uvm_fatal(get_name() , $sformatf(
                    "uvm_config_db #( axi4_bfm_type )::get cannot find resource %s", intf_name))
        end
        begin
            string intf_name = "AXI4_SLAVE_IF";
            if(!uvm_resource_db #( axi4_bfm_type )::read_by_name( get_full_name(),
                intf_name, axi4_slave_config.m_bfm )) `uvm_fatal(get_name() , $sformatf(
                    "uvm_config_db #( axi4_bfm_type )::get cannot find resource %s", intf_name))
        end

    endfunction


    //---------------------------------------------------------
    // Function: set_addr_map
    //---------------------------------------------------------
    
    // Create and set address map.

    virtual function void set_addr_map();

        // Create address map.
        addr_map_t addr_map = addr_map_t::type_id::create("axi4_addr_map");

        // Set address mask (for AXI4 it is 4kB).
        addr_map.addr_mask = 'hf1000;

        // Setup basic full range address space.
        addr_map.add( '{
            kind  : MAP_NORMAL,
            name  : "axi4_addr_map",
            id    : -1,
            domain: MAP_NS,
            region: 0,
            addr  : 'b0,
            size  : 2**axi4lite_misty_pkg::AXI4_ADDR_WIDTH,
            mem   : MEM_DEVICE
            // No 'prot', because no protection support
            // MAP_PROT_ATTR define is not passed to testbench.
        });

        // Pass address map to AXI4 configs.
        axi4_master_config.addr_map = addr_map;
        axi4_slave_config.addr_map = addr_map;

    endfunction


    //---------------------------------------------------------
    // Function: set_master_basic
    //---------------------------------------------------------
    
    // Configure AXI4 masters scoreboarding, assertions and etc.

    virtual function void set_master_basic();

        // Configure master.
        axi4_master_config.agent_cfg.agent_type = AXI4_MASTER;

        // Enable default scoreboarding.
        axi4_master_config.agent_cfg.en_sb = 1'b0;

        // Enable assertions.
        axi4_master_config.m_bfm.config_enable_all_assertions = 1'b1;

        // Enable ready delays from delay db.
        axi4_master_config.en_ready_control = 1; 

        // Address phase is always first.
        // Not in case if we run phase sequences independently.
        // See ~axi4lite_wr_addr_seq_base~, ~axi4lite_wr_data_seq_base~,
        // ~axi4lite_wr_resp_seq_base~ in axi4lite_loopback_seq_lib.sv
        axi4_master_config.m_bfm.config_write_ctrl_first_ratio = 1;
        axi4_master_config.m_bfm.config_write_data_first_ratio = 0;

    endfunction


    //---------------------------------------------------------
    // Function: set_master_delay
    //---------------------------------------------------------
    
    // Set AXI4 master read and write delays.

    virtual function void set_master_delay();

        axi4_master_rd_delay_s min_rd_delay; int unsigned rd_delay;
        axi4_master_rd_delay_s max_rd_delay;
        axi4_master_wr_delay_s min_wr_delay; int unsigned wr_delay;
        axi4_master_wr_delay_s max_wr_delay;

        // Create and configure AXI4 master delay.
        axi4_master_delay = axi4_master_delay_t::type_id::create("master_delay");
        axi4_master_delay.set_config(axi4_master_config);

        // Set default delays for master read database.
        min_rd_delay.rvalid2rready = '{ 0};
        max_rd_delay.rvalid2rready = '{10};
        axi4_master_delay.set_rd_def_delays(min_rd_delay, max_rd_delay);

        // Set default delays for master write database.
        min_wr_delay.addr2data     = '{ 0};
        min_wr_delay.data2data     = '{ 0};
        min_wr_delay.bvalid2bready = '{ 0};
        max_wr_delay.addr2data     = '{10};
        max_wr_delay.data2data     = '{10};
        max_wr_delay.bvalid2bready = '{10};
        axi4_master_delay.set_wr_def_delays(min_wr_delay, max_wr_delay);

        // Pass AXI4 master delay to config.
        axi4_master_config.master_delay = axi4_master_delay;

    endfunction


    //---------------------------------------------------------
    // Function: set_slave_basic
    //---------------------------------------------------------
    
    // Configure AXI4 slaves's scoreboarding, assertions and etc.

    virtual function void set_slave_basic();

        // Configure slave.
        axi4_slave_config.agent_cfg.agent_type = AXI4_SLAVE;

        // Disable default scoreboarding.
        axi4_slave_config.agent_cfg.en_sb = 1'b0;

        // Enable assertions.
        axi4_slave_config.m_bfm.config_enable_all_assertions = 1'b1;

        // Disable assertions on protection.
        // We do not support this signals.
        axi4_slave_config.m_bfm.config_enable_assertion[AXI4_ARPROT_UNKN] = 1'b0;
        axi4_slave_config.m_bfm.config_enable_assertion[AXI4_AWPROT_UNKN] = 1'b0;

        // Enable ready delays from delay db
        axi4_slave_config.en_ready_control = 1;

        // Set slave ID to - 1
        // We do not want to check address map because we must
        // process every incoming ID on every possible address.
        axi4_slave_config.slave_id = -1;

    endfunction


    //---------------------------------------------------------
    // Function: set_slave_delay
    //---------------------------------------------------------
    
    // Set AXI4 slave read and write delays.

    virtual function void set_slave_delay();

        // Setup delays depending on AXI4 slave delay mode.
        // For for example it is 50% chance for zero delay.
        if( $urandom_range(0, 1) )
            set_slave_delay_zero();
        else
            set_slave_delay_nonzero();

    endfunction


    //---------------------------------------------------------
    // Function: set_slave_delay_zero
    //---------------------------------------------------------
    
    // Set zero delays for AXI4 slave

    virtual function void set_slave_delay_zero();

        axi4_slave_delay = axi4_slave_delay_t::type_id::create("axi4_slave_delay");

        // Set full random ready mode.
        axi4_slave_delay.m_random_ready_mode = 1;
        axi4_slave_delay.m_valid2ready_mode  = 0;

        // Set ready always to 1.
        axi4_slave_delay.m_aw_not_ready.min = 0;
        axi4_slave_delay.m_aw_not_ready.max = 0;
        axi4_slave_delay.m_ar_not_ready     = 0;
        axi4_slave_delay.m_ar_not_ready     = 0;
        axi4_slave_delay.m_w_not_ready      = 0;
        axi4_slave_delay.m_w_not_ready      = 0;


        // Set address map.
        axi4_slave_delay.set_address_map(axi4_slave_config.addr_map);

        // Pass AXI4 master delay to config.
        axi4_slave_config.slave_delay = axi4_slave_delay;

    endfunction


    //---------------------------------------------------------
    // Function: set_slave_delay_nonzero
    //---------------------------------------------------------
    
    // Set custom delays for AXI4 slave.

    virtual function void set_slave_delay_nonzero();

        axi4_slave_rd_delay_s min_rd_delay; int unsigned rd_delay;
        axi4_slave_rd_delay_s max_rd_delay;
        axi4_slave_wr_delay_s min_wr_delay; int unsigned wr_delay;
        axi4_slave_wr_delay_s max_wr_delay;

        axi4_slave_delay = axi4_slave_delay_t::type_id::create("axi4_slave_delay");

        // Set address map
        axi4_slave_delay.set_address_map(axi4_slave_config.addr_map);

        // Set default delays for slave read database.
        min_rd_delay.arvalid2arready = 0;
        min_rd_delay.addr2data       = 0;
        min_rd_delay.data2data       = {0};
        max_rd_delay.arvalid2arready = 10;
        max_rd_delay.addr2data       = 10;
        max_rd_delay.data2data       = '{10};
  
        // Set default delays for slave read database.
        axi4_slave_delay.set_rd_def_delays(min_rd_delay, max_rd_delay);
  
        // Set default delays for slave write database.
        min_wr_delay.awvalid2awready = 0;
        min_wr_delay.wvalid2wready   = {0};
        min_wr_delay.wlast2bvalid    = 0;
        max_wr_delay.awvalid2awready = 10;
        max_wr_delay.wvalid2wready   = '{10};
        max_wr_delay.wlast2bvalid    = 10;

        // Set default delays for slave write database
        axi4_slave_delay.set_wr_def_delays(min_wr_delay, max_wr_delay);

        // Pass AXI4 master delay to config
        axi4_slave_config.slave_delay = axi4_slave_delay;

    endfunction


    //---------------------------------------------------------
    // Task: end_of_elaboration_phase
    //---------------------------------------------------------
    
    // Setup some logging settings and etc.

    virtual function void end_of_elaboration_phase(uvm_phase phase);
        // Suppress sequence start info from master.
        axi4_master.m_sequencer.set_report_verbosity_level(UVM_LOW);
    endfunction


    // Environment connects monitors analysis ports
    // with scoreboard analysis implementations.

    virtual function void connect_phase(uvm_phase phase);
        axi4_master.ap["trans_ap"].connect(scrb.axil_imp_m);
        axi4_slave.ap["trans_ap"].connect(scrb.axil_imp_s);
    endfunction



endclass
