//---------------------------------------------------------
// Class: FI_scoreboard_base
//---------------------------------------------------------

`uvm_analysis_imp_decl(_in)


class FI_scoreboard_base extends uvm_scoreboard;
    
    `uvm_component_utils(FI_scoreboard_base)



    uvm_analysis_imp_in#(FI_seq_item_base, FI_scoreboard_base) imp_in;

    int item_amount;

    FI_model  model;
    FI_cov_wrapper cov_wrapper;

     mailbox#(FI_seq_item_base) data_in;

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Functions: write_in, write_out, build_phase, reset_phase, main_phase, do_check
    //---------------------------------------------------------


    virtual function void write_in(FI_seq_item_base t);
        FI_seq_item_base t_in;
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

    // virtual task reset_phase(uvm_phase phase);
    //     FI_seq_item_base tmp;
    //     while(data_in.try_get(tmp));
    // endtask

    virtual task main_phase(uvm_phase phase);
        FI_seq_item_base t_in;
        forever begin
            data_in.get(t_in);
            cov_wrapper.sample(t_in);
            do_check(t_in);
        end
    endtask

    virtual function void do_check(
        FI_seq_item_base t_in
    );  
        logic [8:0] keyR;
        logic [6:0] keyL; 
        logic [15:0] plain;
        logic [15:0] sypher;

        keyL = t_in.key [15:9];
        keyR = t_in.key [8:0];
        plain = t_in.plain; 

       foreach (keyL[i]) begin
            model.fill_KI_L(int'(keyL[i]));
        end
        foreach (keyR[i]) begin
            model.fill_KI_R(int'(keyR[i]));
        end
        foreach (plain[i]) begin
            model.fill_plainA(int'(plain[i]));
        end

        model.FI();

        foreach (sypher[i]) begin
            sypher[i] = model.get(i);
        end

        model.delete_array();
        
        if( sypher !== t_in.sypher ) begin
            $error("Error time plain: %h key %h",t_in.plain,t_in.key);
            `uvm_error({get_name(),": BAD"}, $sformatf(
                {"sypher_o isn't correct Real: %h, ",
                    "Expected %h"},t_in.sypher, sypher ));
        end

    endfunction

endclass
