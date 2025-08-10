//---------------------------------------------------------
// Class: axis_misty_scoreboard
//---------------------------------------------------------
`uvm_analysis_imp_decl(_axis_in)
`uvm_analysis_imp_decl(_axis_out)



class axis_misty_scoreboard extends misty_top_scoreboard;
    
    `uvm_component_utils(axis_misty_scoreboard)


    uvm_analysis_imp_axis_in #(mvc_sequence_item_base, axis_misty_scoreboard) axis_imp_in;

    uvm_analysis_imp_axis_out #(mvc_sequence_item_base, axis_misty_scoreboard) axis_imp_out;

    mailbox#(axis_item_t) axis_mbx_in;
    
    mailbox#(axis_item_t) axis_mbx_out;


    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            axis_imp_in         = new("axis_imp_in",  this);
            axis_imp_out         = new("axis_imp_out",  this);
            axis_mbx_in = new();
            axis_mbx_out = new();
    endfunction

    virtual function void write_axis_in(mvc_sequence_item_base t);
        axis_item_t t_in;
        $cast(t_in, t.clone());
        `uvm_info(get_name(), $sformatf("Got item: %s",
            t_in.convert2string()), UVM_DEBUG);
        void'(axis_mbx_in.try_put(t_in));
    endfunction

    virtual function void write_axis_out(mvc_sequence_item_base t);
        axis_item_t t_in;
        $cast(t_in, t.clone());
        `uvm_info(get_name(), $sformatf("Got item: %s",
            t_in.convert2string()), UVM_DEBUG);
        void'(axis_mbx_out.try_put(t_in));
    endfunction

    virtual task main_phase(uvm_phase phase);
        misty_seq_item_base t_in;
        axis_item_t axis_tmp;
        forever begin
            axis_mbx_in.get(axis_tmp);
            data_in.try_get(t_in);
            t_in.text_i = axis_tmp.data;
            axis_mbx_out.get(axis_tmp);
            t_in.text_o = axis_tmp.data; 
            `uvm_info(get_name(), $sformatf("Got item: %s",
            t_in.convert2string()), UVM_DEBUG);           
            cov_wrapper.sample(t_in);
            do_check(t_in);
        end
    endtask

    virtual task reset_phase(uvm_phase phase);
        misty_seq_item_base tmp;
        axis_item_t axis_tmp;
        while(data_in.try_get(tmp));
        while(axis_mbx_in.try_get(axis_tmp));
        while(axis_mbx_out.try_get(axis_tmp));
    endtask

   
   

endclass