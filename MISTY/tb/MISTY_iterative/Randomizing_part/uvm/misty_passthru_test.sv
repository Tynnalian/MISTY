//---------------------------------------------------------
// Class: misty_passthru_test_base
//---------------------------------------------------------

// misty passthrough test.

class misty_passthru_test_base extends KS_test_base;


    `uvm_component_utils(misty_passthru_test_base)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("env",
            KS_env_base::get_type(), misty_passthru_env_base::get_type());
        super.build_phase(phase);
    endfunction


endclass

//---------------------------------------------------------
// Class: misty_passthru_test_sc
//---------------------------------------------------------

// misty passthrough test.

class misty_passthru_test_sc extends misty_passthru_test_base;


    `uvm_component_utils(misty_passthru_test_sc)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.

    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("env",
            misty_passthru_env_base::get_type(), misty_passthru_env_sc::get_type());     
        super.build_phase(phase);
    endfunction


endclass


//---------------------------------------------------------
// Class: misty_passthru_test_reset
//---------------------------------------------------------

// misty passthrough test with 5 reset in a row.

class misty_passthru_test_reset extends misty_passthru_test_base;


    `uvm_component_utils(misty_passthru_test_reset)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build phase.
    int reset_cnt = 0;

    virtual misty_intf vif;



    

    virtual function void randomize_cfg();
        if(!cfg.randomize() with {
            //duration_type == TIME;
            sync_type     == SYNC_BOTH;
            sync_edge     == NEGEDGE;
        }) begin
            `uvm_fatal(get_name(), "Can't randomize 'cfg'!");
        end
    endfunction

    virtual function void build_phase(uvm_phase phase);
        if(!uvm_resource_db#(virtual misty_intf)::read_by_name(
            get_full_name(), "vif", vif)) begin
            `uvm_fatal(get_name(), "Can't get misty_intf!");
        end
        super.build_phase( phase);
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
            begin
                misty_passthru_env_base env_;
                $cast(env_, env);
                env_.misty_agent.seqr.stop_sequences();
            end

            phase.jump(uvm_pre_reset_phase::get());
        end
        phase.drop_objection( this );

    endtask





endclass
