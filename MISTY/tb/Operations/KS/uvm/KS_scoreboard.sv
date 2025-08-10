//---------------------------------------------------------
// Class: KS_scoreboard_base
//---------------------------------------------------------

`uvm_analysis_imp_decl(_in)


class KS_scoreboard_base extends uvm_scoreboard;
    
    `uvm_component_utils(KS_scoreboard_base)



    uvm_analysis_imp_in#(KS_seq_item_base, KS_scoreboard_base) imp_in;

    int item_amount;

    KS_model  model;
    KS_cov_wrapper cov_wrapper;

     mailbox#(KS_seq_item_base) data_in;

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Functions: write_in, write_out, build_phase, reset_phase, main_phase, do_check
    //---------------------------------------------------------


    virtual function void write_in(KS_seq_item_base t);
        KS_seq_item_base t_in;
        $cast(t_in, t.clone());
        `uvm_info(get_name(), $sformatf("Got item %s", t_in.convert2string()), UVM_DEBUG)
        void'(data_in.try_put(t_in));
    endfunction

  

    virtual function void build_phase(uvm_phase phase);
        void'(uvm_resource_db#(int)::read_by_name(get_full_name(), "item_amount", item_amount));
        model = new();
        imp_in      = new("imp_in", this);
        data_in     = new();
        cov_wrapper = new();
    endfunction


    virtual task main_phase(uvm_phase phase);
        KS_seq_item_base t_in;
        forever begin
            data_in.get(t_in);
            cov_wrapper.sample(t_in);
            do_check(t_in);
        end
    endtask

    virtual function void do_check(
        KS_seq_item_base t_in
    );  
        logic [127:0] key;
        logic [255:0] expand_keys; 

        key = t_in.key ;

       foreach (key[i]) begin
            model.fill_K(int'(key[i]));
        end

        model.key_schedule();

        foreach (expand_keys[i]) begin
            expand_keys[i] = model.get(i);
        end

        model.delete_array();

        
        
        if( expand_keys !== t_in.expand_keys ) begin
            $error("Error time  key %h",t_in.key);
            `uvm_error({get_name(),": BAD"}, $sformatf(
                {"expand_keys_o isn't correct Real: %h, ",
                    "Expected %h"},t_in.expand_keys, expand_keys ));
        end

    endfunction

endclass
