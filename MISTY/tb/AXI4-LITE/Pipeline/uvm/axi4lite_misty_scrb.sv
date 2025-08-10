//---------------------------------------------------------
// Class: misty_scoreboard_base
//---------------------------------------------------------

`uvm_analysis_imp_decl(_m)
`uvm_analysis_imp_decl(_s)


class misty_axil_scoreboard_base extends uvm_scoreboard;
    
    `uvm_component_utils(misty_axil_scoreboard_base)

    uvm_analysis_imp_m  #(mvc_sequence_item_base, misty_axil_scoreboard_base) axil_imp_m;

    uvm_analysis_imp_s  #(mvc_sequence_item_base, misty_axil_scoreboard_base) axil_imp_s;

    MISTY_model  model;

    misty_cov_wrapper cov_wrapper;

    mailbox#(misty_seq_item_base) data_in;

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Functions: write_in, write_out, build_phase, reset_phase, main_phase, do_check
    //---------------------------------------------------------


    virtual function void write_m(mvc_sequence_item_base t);
        axi4_master_rw_transaction #(`AXI4_PARAMS_INST) t_in;
        $cast(t_in, t.clone());
        `uvm_info(get_name(), $sformatf("Got item %s", t_in.convert2string()), UVM_DEBUG)
    endfunction


    virtual function void write_s(mvc_sequence_item_base t);
        axi4_master_rw_transaction #(`AXI4_PARAMS_INST) t_in;
        $cast(t_in, t.clone());
        `uvm_info(get_name(), $sformatf("Got item %s", t_in.convert2string()), UVM_DEBUG)
    endfunction
  

    virtual function void build_phase(uvm_phase phase);
        model = new();
        axil_imp_m      = new("axil_imp_m", this);
        axil_imp_s      = new("axil_imp_s", this);
        data_in     = new();
        cov_wrapper = new();
    endfunction

    // virtual task reset_phase(uvm_phase phase);
    //     FO_seq_item_base tmp;
    //     while(data_in.try_get(tmp));
    // endtask

    // virtual task run_phase(uvm_phase phase);
    //     // misty_seq_item_base t_in;
    //     // forever begin
    //     //     // data_in.get(t_in);
    //     //     // cov_wrapper.sample(t_in);
    //     //     // do_check(t_in);
    //     // end
    // endtask

    
endclass