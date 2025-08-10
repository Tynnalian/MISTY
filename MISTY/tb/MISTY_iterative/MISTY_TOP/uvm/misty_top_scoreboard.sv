//---------------------------------------------------------
// Class: misty_scoreboard_base
//---------------------------------------------------------


class misty_top_scoreboard extends misty_scoreboard_base;
    
    `uvm_component_utils(misty_top_scoreboard)


   KS_model  ks_model;


    function new(string name = "", uvm_component parent = null);
        super.new(name, parent);
    endfunction


    virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            ks_model = new();
    endfunction


    virtual function void do_check(
        misty_seq_item_base t_in
    );  
        logic [63:0] text_i;
        logic [63:0] text_o; 
        logic [255:0] key;
        for ( int i=128; i>0; i--)  begin
            ks_model.fill_K(int'(t_in.key[i-1]));
        end

        ks_model.key_schedule();

        foreach (key[i]) begin
            key[i] = ks_model.get(i);
        end

        ks_model.delete_array();


        text_i = t_in.text_i;
        text_o = t_in.text_o;

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
               $error("Error time text_i: %h key %h text_o %h",t_in.text_i,key,t_in.text_o);
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
              $error("Error time text_i: %h key %h text_o %h",t_in.text_i,key,t_in.text_o);
              `uvm_error({get_name(),": BAD"}, $sformatf(
                {"DECR_MODE text_o isn't correct Real: %h, ",
                    "Expected %h"},t_in.text_o, text_o ));
            end
        end  
    endfunction

endclass