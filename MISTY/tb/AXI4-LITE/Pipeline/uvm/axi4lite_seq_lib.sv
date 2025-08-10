//---------------------------------------------------------
// Library: axi4_loopback_seq_lib
//---------------------------------------------------------

// Sequence library for AXI4-Lite VIP loopback.


//---------------------------------------------------------
// Class: axi4lite_seq_base
//---------------------------------------------------------

// Base AXI4-Lite sequence.
// Contains transactions amount field, transactions array
// and basic methods for manipulation with transactions.

class axi4lite_seq_base extends axi4_master_deparam_seq;

    `uvm_object_utils(axi4lite_seq_base)
    `uvm_object_new


    //---------------------------------------------------------
    // Field: trans_amount
    //---------------------------------------------------------

    // Transactions amount.
    // Can be set explicitly or randomized.
    
    rand int unsigned trans_amount;


    //---------------------------------------------------------
    // Field: transactions
    //---------------------------------------------------------
    
    // Transactions arrays.

    mvc_sequence transactions [];
    axi4_phase_t phases       [];


    //---------------------------------------------------------
    // Field: host_agent
    //---------------------------------------------------------

    // Host agent (on which sequencer sequence is executed)

    axi4_agent_t host_agent; 


    //---------------------------------------------------------
    // Function: configure
    //---------------------------------------------------------

    // This function is used for sequence configuration.
    
    virtual function void configure();
        // Get host agent.
        get_host_agent();
    endfunction


    //---------------------------------------------------------
    // Function: get_host_agent
    //---------------------------------------------------------

    // This function gets host agent

    virtual function void get_host_agent();
        uvm_sequencer_base host_sequencer;
        host_sequencer = get_sequencer();
        $cast(host_agent, host_sequencer.get_parent());
    endfunction


    //---------------------------------------------------------
    // Task: body
    //---------------------------------------------------------

    // Main body task with calling virtual method for running
    // sequences by default.
    
    virtual task body();
        host_agent.cfg.wait_for_reset();
        super.body();
        run_seqs();
    endtask


    //---------------------------------------------------------
    // Task: run_seqs
    //---------------------------------------------------------

    // Called inside ~body()~.
    // Used for creating and running transactions.

    virtual task run_seqs();
        // Create and randomize transactions.
        transactions = new[trans_amount];
        foreach (transactions[i]) begin
            transactions[i] = get_trans();
            transactions[i].set_sequencer(m_sequencer);
            rand_trans(transactions[i]);
        end
        // Run transactions.
        foreach(transactions[i]) begin
            transactions[i].start(m_sequencer);
        end
    endtask


    //---------------------------------------------------------
    // Task: run_phases
    //---------------------------------------------------------

    // Can be called inside ~body()~.
    // Used for creating and running phases.

    virtual task run_phases();
        // Create and randomize phases.
        phases = new[trans_amount];
        foreach (phases[i]) begin
            phases[i] = get_phase();
            phases[i].set_sequencer(m_sequencer);
            rand_phase(phases[i]);
        end
        // Run phases.
        foreach(phases[i]) begin
            start_item (phases[i]);
            finish_item(phases[i]);
        end
    endtask


    //---------------------------------------------------------
    // Function: rand_trans
    //---------------------------------------------------------

    // Function for randomization of transaction.
    
    virtual function void rand_trans(mvc_sequence seq);
        if(!seq.randomize()) begin
            `uvm_fatal(get_name(), "Can't randomize AXI4 sequence!");
        end
    endfunction


    //---------------------------------------------------------
    // Function: get_trans
    //---------------------------------------------------------
    
    // Function for getting transaction.

    virtual function  mvc_sequence get_trans();
        `uvm_fatal(get_name(),
            "This function must be overriden in child class!");
    endfunction


    //---------------------------------------------------------
    // Function: rand_phase
    //---------------------------------------------------------

    // Function for randomization of phase.
    
    virtual function void rand_phase(axi4_phase_t phase);
        if(!phase.randomize()) begin
            `uvm_fatal(get_name(), "Can't randomize AXI4 phase!");
        end
    endfunction

    //---------------------------------------------------------
    // Function: get_phase
    //---------------------------------------------------------
    
    // Function for getting phase.

    virtual function axi4_phase_t get_phase();
        `uvm_fatal(get_name(),
            "This function must be overriden in child class!");
    endfunction

endclass


//---------------------------------------------------------
// Class: axi4lite_wr_seq_base
//---------------------------------------------------------

// This AXI4-lite write sequence.
// Runs multiple AXI4-Lite write transactions.

class axi4lite_wr_seq_base extends axi4lite_seq_base;

    `uvm_object_utils(axi4lite_wr_seq_base)
    `uvm_object_new


    //---------------------------------------------------------
    // Typedef: wr_trans_t
    //---------------------------------------------------------

    typedef axi4lite_wr_data_deparam_seq wr_trans_t;


    //---------------------------------------------------------
    // Function: get_trans
    //---------------------------------------------------------

    virtual function mvc_sequence get_trans();
        wr_trans_t wr_trans = wr_trans_t::type_id::create("axi4_wr_trans_t");
        return wr_trans;
    endfunction

    //---------------------------------------------------------
    // Function: rand_trans
    //---------------------------------------------------------
    
    // virtual function void rand_trans(mvc_sequence seq);
    //     wr_trans_t wr_trans;
    //     $cast(wr_trans, seq);
    //     if(!wr_trans.randomize() with {write_strobes == 8'hFF;}) begin
    //         `uvm_fatal(get_name(), "Can't randomize AXI4 sequence!");
    //     end
    // endfunction


endclass


//---------------------------------------------------------
// Class: axi4lite_rd_seq_base
//---------------------------------------------------------

// This AXI4-lite read sequence.
// Runs multiple AXI4-Lite read transactions.

class axi4lite_rd_seq_base extends axi4lite_seq_base;

    `uvm_object_utils(axi4lite_rd_seq_base)
    `uvm_object_new


    //---------------------------------------------------------
    // Typedef: rd_trans_t
    //---------------------------------------------------------

    typedef axi4lite_rd_data_deparam_seq rd_trans_t;


    //---------------------------------------------------------
    // Function: get_trans
    //---------------------------------------------------------

    virtual function mvc_sequence get_trans();
        rd_trans_t rd_trans = rd_trans_t::type_id::create("axi4_rd_trans_t");
        return rd_trans;
    endfunction

    //---------------------------------------------------------
    // Function: rand_trans
    //---------------------------------------------------------
    
    virtual function void rand_trans(mvc_sequence seq);
        rd_trans_t rd_trans;
        $cast(rd_trans, seq);
        if(!rd_trans.randomize() with {addr inside {[2:32]};}) begin
            `uvm_fatal(get_name(), "Can't randomize AXI4 sequence!");
        end
    endfunction


endclass


//---------------------------------------------------------
// Class: axi4lite_wr_addr_seq_base
//---------------------------------------------------------

// This AXI4-lite write address sequence.
// Runs multiple AXI4-Lite write address channel transactions.

class axi4lite_wr_addr_seq_base extends axi4lite_seq_base;

    `uvm_object_utils(axi4lite_wr_addr_seq_base)
    `uvm_object_new


    //---------------------------------------------------------
    // Typedef: wr_addr_t
    //---------------------------------------------------------

    typedef axi4_master_write_addr_channel_phase#(`AXI4_PARAMS_INST) wr_addr_t;


    //---------------------------------------------------------
    // Task: body
    //---------------------------------------------------------
    
    virtual task body();
        run_phases();
    endtask


    //---------------------------------------------------------
    // Function: get_phase
    //---------------------------------------------------------

    virtual function axi4_phase_t get_phase();
        wr_addr_t wr_addr = wr_addr_t::type_id::create("axi4_wr_addr");
        return wr_addr;
    endfunction


    //---------------------------------------------------------
    // Function: rand_phase
    //---------------------------------------------------------

    virtual function void rand_phase(axi4_phase_t phase);
        wr_addr_t wr_addr;
        $cast(wr_addr, phase);
        // Align address to avoid strobe mismatch at data phase.
        if(!wr_addr.randomize() with {addr[1:0] == 2'b00;}) begin
            `uvm_fatal(get_name(), "Can't randomize AXI4 phase!");
        end
    endfunction


endclass


//---------------------------------------------------------
// Class: axi4lite_wr_data_seq_base
//---------------------------------------------------------

// This AXI4-lite write data sequence.
// Runs multiple AXI4-Lite write data channel transactions.

class axi4lite_wr_data_seq_base extends axi4lite_seq_base;

    `uvm_object_utils(axi4lite_wr_data_seq_base)
    `uvm_object_new


    //---------------------------------------------------------
    // Typedef: wr_data_t
    //---------------------------------------------------------

    typedef axi4_master_write_channel_phase#(`AXI4_PARAMS_INST) wr_data_t;


    //---------------------------------------------------------
    // Task: body
    //---------------------------------------------------------
    
    virtual task body();
        run_phases();
    endtask


    //---------------------------------------------------------
    // Function: get_trans
    //---------------------------------------------------------

    virtual function axi4_phase_t get_phase();
        wr_data_t wr_data = wr_data_t::type_id::create("axi4_wr_data");
        return wr_data;
    endfunction


endclass
