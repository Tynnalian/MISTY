
//---------------------------------------------------------
// Class: FI_test_base
//---------------------------------------------------------

// Base test for FI

class FI_test_base extends uvm_test;

    `uvm_component_utils(FI_test_base)

    FI_env_base env;

    //---------------------------------------------------------
    // Field: Agent with config.
    //---------------------------------------------------------

    reset_agent     ag;
    reset_agent_cfg cfg;
   
    // FI_intf
    virtual FI_intf vif; 

    
    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        if (!uvm_resource_db#(virtual FI_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
            `uvm_fatal(get_name(), "Can't get FI_intf!");
        end
        uvm_resource_db#(int)::set(
           "*", "item_amount", $urandom_range(100, 500), this
        );
        uvm_resource_db#(int)::set(
           "*", "write_delay_max", 10, this
        );
        uvm_resource_db#(int)::set(
           "*", "write_delay_min", 0, this
        );
        env = FI_env_base::type_id::create("env", this);

        cfg = reset_agent_cfg::type_id::create("cfg");
        randomize_cfg();
        uvm_resource_db#(reset_agent_cfg)::set(
            {get_full_name(), ".*"}, "cfg", cfg);
        ag = reset_agent::type_id::create("ag", this);

    endfunction

    virtual task main_phase(uvm_phase phase);
        FI_seq_base seq;
        phase.raise_objection(this);
        seq = FI_seq_base::type_id::create("seq");
        seq.start(env.agent.seqr);
        phase.drop_objection(this);
    endtask

        //---------------------------------------------------------
    // Function: randomize_cfg
    //---------------------------------------------------------
    
    // Agent configuration randomization.

    virtual function void randomize_cfg();
        if(!cfg.randomize()) begin
            `uvm_fatal(get_name(), "Can't randomize 'cfg'!");
        end
    endfunction


    //---------------------------------------------------------
    // Tasks: UVM phases
    //---------------------------------------------------------
    
    virtual task reset_phase(uvm_phase phase);
        reset_seq seq;
        phase.raise_objection(this);
        seq = reset_seq::type_id::create("seq");
        seq.start(ag.sqr);
        phase.drop_objection(this);
    endtask


endclass

//---------------------------------------------------------
// Class: FI_test_reset
//---------------------------------------------------------

// Base test for FI with reset in the middle

class FI_test_reset extends FI_test_base;

    `uvm_component_utils(FI_test_reset)

    bit reset_done = 0;

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

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
        if (!reset_done) begin
            vif.wait_for_clks(100);
            // while(vif.is_handshake())
            //     vif.wait_for_clks(1);
           reset_done = 1;
 
           env.agent.seqr.stop_sequences(); 
            phase.jump(uvm_pre_reset_phase::get());
        end
        phase.drop_objection( this );

    endtask

endclass




