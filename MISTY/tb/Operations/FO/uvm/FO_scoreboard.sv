//---------------------------------------------------------
// Class: FO_scoreboard_base
//---------------------------------------------------------

`uvm_analysis_imp_decl(_in)


class FO_scoreboard_base extends uvm_scoreboard;
    
    `uvm_component_utils(FO_scoreboard_base)



    uvm_analysis_imp_in#(FO_seq_item_base, FO_scoreboard_base) imp_in;

    int item_amount;

    FO_model  model;
    FO_cov_wrapper cov_wrapper;

     mailbox#(FO_seq_item_base) data_in;

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Functions: write_in, write_out, build_phase, reset_phase, main_phase, do_check
    //---------------------------------------------------------


    virtual function void write_in(FO_seq_item_base t);
        FO_seq_item_base t_in;
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
        FO_seq_item_base t_in;
        forever begin
            data_in.get(t_in);
            cov_wrapper.sample(t_in);
            do_check(t_in);
        end
    endtask

    virtual function void do_check(
        FO_seq_item_base t_in
    );  
        logic [47:0] keyI;
        logic [63:0] keyO; 
        logic [31:0] plain;
        logic [31:0] sypher;


        keyI = t_in.key_I;
        keyO = t_in.key_O ;
        plain = t_in.plain; 

      foreach (keyI[i]) begin
            model.fill_KI_mas(int'(keyI[i]));
        end
        foreach (keyO[i]) begin
            model.fill_KO_mas(int'(keyO[i]));
        end
        foreach (plain[i]) begin
            model.fill_plainA(int'(plain[i]));
        end


        model.FO();

        foreach (sypher[i]) begin
            sypher[i] = model.get(i);
        end

        model.delete_array();
        
        if( sypher !== t_in.sypher ) begin
            $error("Error time plain: %h key_I %h key_O %h",t_in.plain,t_in.key_I,t_in.key_O);
            `uvm_error({get_name(),": BAD"}, $sformatf(
                {"sypher_o isn't correct Real: %h, ",
                    "Expected %h"},t_in.sypher, sypher ));
        end

    endfunction

endclass
