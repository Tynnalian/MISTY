//---------------------------------------------------------
// Class: misty_test_pipe
//---------------------------------------------------------

// misty top test for pipeline version.

class misty_test_pipe extends misty_test_base;

    `uvm_component_utils(misty_test_pipe)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("env",
            misty_env_base::get_type(), misty_env_pipe::get_type());     
        super.build_phase(phase);   
    endfunction

endclass

//---------------------------------------------------------
// Class: misty_pipe_test_reset
//---------------------------------------------------------

// misty passthrough test with 5 reset in a row.

class misty_test_pipe_reset extends misty_test_pipe;


    `uvm_component_utils(misty_test_pipe_reset)

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
        //FO_seq_base seq;
        phase.raise_objection( this );
        fork
        super.main_phase( phase );
        join_none
        if (reset_cnt < 5) begin
           if (reset_cnt == 0) begin 
               env.agent.drv.vif.wait_for_clks(1000);
               reset_cnt ++;   
           end 
           else begin
               env.agent.drv.vif.wait_for_clks($urandom_range(500,1000));
               reset_cnt ++;        
           end
             while(env.agent.drv.vif.valid_i)
                env.agent.drv.vif.wait_for_clks(1);  
        // // Завершаем последовательность
            env.agent.seqr.stop_sequences();
        // // Переход в фазу сброса
            phase.jump(uvm_pre_reset_phase::get());
        end
        phase.drop_objection( this );

    endtask

endclass 

//---------------------------------------------------------
// Class: misty_test_stall
//---------------------------------------------------------

// misty top test for pipeline version with stall_driver.

class misty_test_stall extends misty_test_pipe;

    `uvm_component_utils(misty_test_stall)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("env",
            misty_env_base::get_type(), misty_env_pipe::get_type());  
        set_inst_override_by_type("env.agent.drv",
            misty_driver_pipe::get_type(), misty_driver_pipe_stall::get_type());    
        super.build_phase(phase);    
    endfunction

endclass


//---------------------------------------------------------
// Class: misty_test_stall_valid
//---------------------------------------------------------

// misty top test for pipeline with misty_driver_valid_stall.

class misty_test_stall_valid extends misty_test_pipe;

    `uvm_component_utils(misty_test_stall_valid)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("env",
            misty_env_base::get_type(), misty_env_pipe::get_type());
        set_inst_override_by_type("env.agent.drv",
            misty_driver_pipe::get_type(), misty_driver_valid_stall::get_type());    
        super.build_phase(phase);    
    endfunction

endclass

//---------------------------------------------------------
// Class: misty_test_sc
//---------------------------------------------------------

// misty top test with self_check.

class misty_test_pipe_sc extends misty_test_base;


    `uvm_component_utils(misty_test_pipe_sc)

    // Constructor.

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        set_inst_override_by_type("env",
            misty_env_base::get_type(), misty_env_pipe_sc::get_type());       
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