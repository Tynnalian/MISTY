//---------------------------------------------------------
// Class: misty_test_base
//---------------------------------------------------------

// Base test for misty

class misty_test_base extends uvm_test;

    `uvm_component_utils(misty_test_base)

    misty_env_base env;

    //---------------------------------------------------------
    // Field: Agent with config.
    //---------------------------------------------------------

    reset_agent     ag;
    reset_agent_cfg cfg;

    virtual misty_intf vif;
    
    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);

        if (!uvm_resource_db#(virtual misty_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
            `uvm_fatal(get_name(), "Can't get misty_intf!");
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
        env = misty_env_base::type_id::create("env", this);

        cfg = reset_agent_cfg::type_id::create("cfg");
        randomize_cfg();
        uvm_resource_db#(reset_agent_cfg)::set(
            {get_full_name(), ".*"}, "cfg", cfg);
        ag = reset_agent::type_id::create("ag", this);

    endfunction

    virtual task main_phase(uvm_phase phase);
        misty_seq_base seq;
        phase.raise_objection(this);
        seq = misty_seq_base::type_id::create("seq");
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
// Class: misty_test_reset
//---------------------------------------------------------

// misty  test with 5 reset in a row.

class misty_test_reset extends misty_test_base;


    `uvm_component_utils(misty_test_reset)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.
    int reset_cnt = 0;

 

    virtual function void randomize_cfg();
        if(!cfg.randomize() with {
            //duration_type == TIME;
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
               vif.wait_for_clks(1000);
               reset_cnt ++;   
           end 
           else begin
               vif.wait_for_clks($urandom_range(500,1000));
               reset_cnt ++;        
           end
             while(vif.is_handshake())
                vif.wait_for_clks(1);  
            env.agent.seqr.stop_sequences();
            phase.jump(uvm_pre_reset_phase::get());
        end
        phase.drop_objection( this );

    endtask





endclass

//---------------------------------------------------------
// Class: misty_test_sc
//---------------------------------------------------------

// misty top test with self_check.

class misty_test_sc extends misty_test_base;


    `uvm_component_utils(misty_test_sc)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("env",
            misty_env_base::get_type(), misty_env_sc::get_type());   
        super.build_phase(phase);       
    endfunction


    virtual task main_phase(uvm_phase phase);
        misty_seq_sc seq;
        phase.raise_objection(this);
        seq = misty_seq_sc::type_id::create("seq");
        seq.start(env.agent.seqr);
        phase.drop_objection(this);
    endtask


endclass
