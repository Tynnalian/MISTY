//---------------------------------------------------------
// Class: misty_scoreboard_base
//---------------------------------------------------------

`uvm_analysis_imp_decl(_in)


class misty_scoreboard_base extends uvm_scoreboard;
    
    `uvm_component_utils(misty_scoreboard_base)

    uvm_analysis_imp_in#(misty_seq_item_base, misty_scoreboard_base) imp_in;

    int item_amount;

    MISTY_model  model;

    misty_cov_wrapper cov_wrapper;

    mailbox#(misty_seq_item_base) data_in;

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    //---------------------------------------------------------
    // Functions: write_in, write_out, build_phase, reset_phase, main_phase, do_check
    //---------------------------------------------------------


    virtual function void write_in(misty_seq_item_base t);
        misty_seq_item_base t_in;
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
        misty_seq_item_base t_in;
        forever begin
            data_in.get(t_in);
            cov_wrapper.sample(t_in);
            do_check(t_in);
        end
    endtask

    virtual function void do_check(
        misty_seq_item_base t_in
    );  
        logic [63:0] text_i;
        logic [63:0] text_o; 
        logic [255:0] key;

        text_i = t_in.text_i;
        text_o = t_in.text_o;
        key    = t_in.key;

        if (t_in.enc) begin
            
            foreach (text_i[i]) begin
              model.fill_plainA(int'(text_i[i]));
            end

            foreach (key[i]) begin
              model.fill_exp_key(int'(key[i]));
            end

            model.Encryption_Mode();

            foreach (text_o[i]) begin
            text_o[i] = model.get_sypher(i);
            end

            model.delete_array();

            if( text_o !== t_in.text_o ) begin
               $error("Error time text_i: %h key %h text_o %h",t_in.text_i,t_in.key,t_in.text_o);
               `uvm_error({get_name(),": BAD"}, $sformatf(
                {"ENC_MODE text_o isn't correct Real: %h, ",
                    "Expected %h"},t_in.text_o, text_o ));
            end
        end
        else begin            
            model.delete_array();
            foreach (text_i[i]) begin
              model.fill_sypher(int'(text_i[i]));
            end

            foreach (key[i]) begin
              model.fill_exp_key(int'(key[i]));
            end

            model.Decryption_Mode();
        
            foreach (text_o[i]) begin
              text_o[i] = model.get_plain(i);
            end

            model.delete_array();

            if( text_o !== t_in.text_o ) begin
              $error("Error time text_i: %h key %h text_o %h",t_in.text_i,t_in.key,t_in.text_o);
              `uvm_error({get_name(),": BAD"}, $sformatf(
                {"DECR_MODE text_o isn't correct Real: %h, ",
                    "Expected %h"},t_in.text_o, text_o ));
            end
        end  
    endfunction

endclass


class misty_scoreboard_sc extends misty_scoreboard_base;
    
    `uvm_component_utils(misty_scoreboard_sc)

  

    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    virtual task main_phase(uvm_phase phase);
        misty_seq_item_base t_enc;
        misty_seq_item_base t_dec;
        forever begin
            data_in.get(t_enc);
            cov_wrapper.sample(t_enc);
            data_in.get(t_dec);
            cov_wrapper.sample(t_dec);
            sc_check(t_enc,t_dec);
        end
    endtask


    virtual function void sc_check(
        misty_seq_item_base t_enc,
        misty_seq_item_base t_dec
    );  
         if( t_enc.text_o !== t_dec.text_i ) begin
               `uvm_error({get_name(),": BAD"}, $sformatf(
                {"SELF_check text_o isn't text_i on the second part of transaction Real: %h, ",
                    "Expected %h"},t_enc.text_o, t_dec.text_i ));
            end
          if( t_enc.enc === t_dec.enc ) begin
               `uvm_error({get_name(),": BAD"}, $sformatf(
                {"SELF_check  isn't enc=0 on the second part of transaction Real: %h, ",
                    "Expected %h"},t_enc.enc, t_dec.enc ));
            end
          if( t_enc.text_i !== t_dec.text_o ) begin
               `uvm_error({get_name(),": BAD"}, $sformatf(
                {"SELF_check text_i isn't decrypted text Real: %h, ",
                    "Expected %h"},t_dec.text_o, t_enc.text_i ));
            end                          
          if( t_enc.key !== t_dec.key ) begin
               `uvm_error({get_name(),": BAD"}, $sformatf(
                {"SELF_CHECK keys aren`t same Real: %h, ",
                    "Expected %h"},t_enc.key, t_dec.key ));
            end
 
    endfunction



   

endclass