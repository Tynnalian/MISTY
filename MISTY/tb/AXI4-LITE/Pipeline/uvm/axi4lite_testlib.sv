//---------------------------------------------------------
// Library: axi4lite_misty_test_lib
//---------------------------------------------------------

// Test library for AXI4-Lite VIP misty.


//---------------------------------------------------------
// Class: axi4lite_misty_test_base
//---------------------------------------------------------

// Base test for AXI4-Lite VIP loopback.

class axi4lite_misty_test_base extends uvm_test;

    `uvm_component_utils(axi4lite_misty_test_base)
    `uvm_component_new


    //---------------------------------------------------------
    // Field: env
    //---------------------------------------------------------
    
    // Environment for AXI4-Lite VIP loopback.

    axi4lite_misty_env env;


    //---------------------------------------------------------
    // Fields: AXI4-Lite write and read sequences
    //---------------------------------------------------------

    axi4lite_seq_base axi4_w_seqs [$];
    axi4lite_seq_base axi4_r_seqs [$];

    //---------------------------------------------------------
    // Fields: reset agent reset_cfg
    //---------------------------------------------------------
    
    //Agent for for reset test 

    reset_agent     ag;
    reset_agent_cfg rst_cfg; 


    //---------------------------------------------------------
    // Function: randomize_rst_cfg
    //---------------------------------------------------------
    
    // Agent configuration randomization.

    virtual function void randomize_rst_cfg();
        if(!rst_cfg.randomize()) begin
            `uvm_fatal(get_name(), "Can't randomize 'cfg'!");
        end
    endfunction

    //---------------------------------------------------------
    // Field: enc_cfg dec_cfg
    //---------------------------------------------------------
    
    // CFG for enc_agent and dec_agent.

    gpio_agent_cfg enc_gpio_cfg;
    gpio_agent_cfg dec_gpio_cfg;

    
    //---------------------------------------------------------
    // Fields: Settings
    //---------------------------------------------------------
    
    // Can be incapsulated in test configuration class.

    int unsigned seq_am           = 10;
    int unsigned trans_per_seq_am  = 15;
    int unsigned seq_timeout_clks = 1_000_000;


    //---------------------------------------------------------
    // Function: build_phase
    //---------------------------------------------------------
    
    // Create AXI4-Lite environment.

    virtual function void build_phase(uvm_phase phase);
        env = axi4lite_misty_env::type_id::create("env", this);
        misty_ag_cfg();
        rst_ag_cfg  ();
        gpio_ag_cfg();
    endfunction
    


    //---------------------------------------------------------
    // Function: misty_ag_cfg
    //---------------------------------------------------------
    
    // function for creating and configure misty agent

    virtual function void misty_ag_cfg();
        uvm_resource_db#(int)::set(
           "*", "item_amount", 1, this
        );
        uvm_resource_db#(int)::set(
           "*", "write_delay_max", 1, this
        );
        uvm_resource_db#(int)::set(
           "*", "write_delay_min", 0, this
        );
    endfunction



    //---------------------------------------------------------
    // Function: gpio_ag_cfg
    //---------------------------------------------------------
    
    // function for creating and configure gpio agents

    virtual function void gpio_ag_cfg();
        enc_gpio_cfg = gpio_agent_cfg::type_id::create("enc_gpio_cfg");
        dec_gpio_cfg = gpio_agent_cfg::type_id::create("dec_gpio_cfg");
        enc_gpio_cfg.get_width(get_full_name());
        dec_gpio_cfg.get_width(get_full_name());
        uvm_resource_db#(gpio_agent_cfg)::set(
            "uvm_test_top.env.enc_ag*", "cfg", enc_gpio_cfg);
        uvm_resource_db#(gpio_agent_cfg)::set(
            "uvm_test_top.env.dec_ag*", "cfg", dec_gpio_cfg);

    endfunction


    //---------------------------------------------------------
    // Function: rst_ag_cfg
    //---------------------------------------------------------
    
    // function for creating and configure reset agent

    virtual function void rst_ag_cfg();
        rst_cfg = reset_agent_cfg::type_id::create("rst_cfg");
        randomize_rst_cfg();
        uvm_resource_db#(reset_agent_cfg)::set(
            {get_full_name(), ".*"}, "cfg", rst_cfg);
        ag = reset_agent::type_id::create("ag", this);
    endfunction


    //---------------------------------------------------------
    // Task: run_phase
    //---------------------------------------------------------
    
    // Main stimulus here.

    virtual task main_phase(uvm_phase phase);
        misty_seq_base key_seq;
        gpio_seq  enc_gpio_seq,dec_gpio_seq;
        phase.raise_objection(this);

        // Create sequences.
        key_seq = misty_seq_base::type_id::create("misty_seq");
        enc_gpio_seq=create_enc_gpio_seq();
        dec_gpio_seq=create_dec_gpio_seq();
        create_axi4_w_seqs();
        create_axi4_r_seqs();
        
        // Run sequences.
        // This task will end if all sequences are
        // done or if any sequence is timeouted.
        key_seq.start(env.misty_agent.seqr);
        enc_gpio_seq.start(env.enc_ag.sqr);
        dec_gpio_seq.start(env.dec_ag.sqr);
        run_seqs();

        phase.drop_objection(this);

    endtask


    //---------------------------------------------------------
    // Function: create_axi4_w_seqs
    //---------------------------------------------------------

    // This function creates write sequences to run.

    virtual function void create_axi4_w_seqs();
        axi4lite_wr_seq_base seq;
        // Run random write sequences.
        repeat(seq_am) begin
            seq = axi4lite_wr_seq_base::type_id::create("wr_seq");
            seq.set_sequencer(env.axi4_master.m_sequencer);
            seq.trans_amount = trans_per_seq_am;
            seq.configure();
            axi4_w_seqs.push_back(seq);
        end
    endfunction


    //---------------------------------------------------------
    // Function: create_axi4_r_seqs
    //---------------------------------------------------------

    // This function creates read sequences to run.

    virtual function void create_axi4_r_seqs();
        axi4lite_rd_seq_base seq;
        // Run random read sequences.
        repeat(seq_am) begin
            seq = axi4lite_rd_seq_base::type_id::create("rd_seq");
            seq.set_sequencer(env.axi4_master.m_sequencer);
            seq.trans_amount = trans_per_seq_am;
            seq.configure();
            axi4_r_seqs.push_back(seq);
        end
    endfunction


    //---------------------------------------------------------
    // Task: run_axi4_seqs
    //---------------------------------------------------------
    
    // This task runs AXI4 sequences.

    virtual task run_seqs();
        fork
            begin
                run_axi4_seq_queue(axi4_w_seqs);
            end
            begin
                run_axi4_seq_queue(axi4_r_seqs);
            end
        join
    endtask


    //---------------------------------------------------------
    // Task: run_axi4_seq_queue
    //---------------------------------------------------------

    // This task runs sequences queue on master sequencer.

    virtual task run_axi4_seq_queue(
        axi4lite_seq_base seqs [$]
    );  

        foreach(seqs[i]) begin
            `uvm_info(get_name(), $sformatf("Running sequence '%s' on AXI4...",
                seqs[i].get_name()), UVM_MEDIUM);
            fork begin
                fork
                    seqs[i].start(env.axi4_master.m_sequencer);
                    // seqs[i].print();
                    seq_timeout();
                join_any
                disable fork;
            end join
        end
    endtask


    //---------------------------------------------------------
    // Tasks: Timeouts
    //---------------------------------------------------------

    // Sequence timeout for AXI4 master.
    // We drop fatal if sequence is timeouted.
    
    virtual task seq_timeout();
        env.axi4_master_config.wait_for_reset();
        repeat(seq_timeout_clks)
            env.axi4_master_config.wait_for_clock();
        `uvm_fatal(get_name(), "Sequence timeout on AXI4 master!");
    endtask

    //---------------------------------------------------------
    // Task: Reset_phase
    //---------------------------------------------------------
    
    virtual task reset_phase(uvm_phase phase);
        reset_seq seq;
        phase.raise_objection(this);
        seq = reset_seq::type_id::create("seq");
        seq.start(ag.sqr);
        phase.drop_objection(this);
    endtask


    //---------------------------------------------------------
    // Function: create_enc_gpio_seq
    //---------------------------------------------------------

    // This function creates enc sequences to run.

    virtual function gpio_seq create_enc_gpio_seq();
        gpio_seq seq;
        seq = gpio_seq::type_id::create("seq");
        seq.init_req();
        seq.rand_req();
        seq.set_range(enc_gpio_cfg.width);
        seq.set_interaction_type(SET_DATA);
        return seq;
    endfunction


    //---------------------------------------------------------
    // Function: create_dec_gpio_seq
    //---------------------------------------------------------

    // This function creates dec sequences to run.

    virtual function gpio_seq create_dec_gpio_seq();
        gpio_seq seq;
        seq = gpio_seq::type_id::create("seq");
        seq.init_req();
        seq.rand_req();
        seq.set_range(dec_gpio_cfg.width);
        seq.set_interaction_type(SET_DATA);
        return seq;
    endfunction



endclass


