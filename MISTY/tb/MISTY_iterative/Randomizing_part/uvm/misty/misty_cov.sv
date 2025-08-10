//---------------------------------------------------------
// Covergroups for functional coverage
//---------------------------------------------------------

// Checking data from input and output transaction

covergroup misty_value_cg with function sample(misty_seq_item_base trans);

    text_i_cp: coverpoint trans.text_i {
        bins b1 [64] = {[0:$]};
    }
    key_cp: coverpoint trans.key {
        bins b1 [100] = {[0:$]};
    }
    text_o_cp: coverpoint trans.text_o {
        bins b1 [1000] = {[0:$]};
    }
    enc_i_cp: coverpoint trans.enc {
        bins b1  = {0,1};
    }

    textXkeyXenc: cross text_i_cp, key_cp, enc_i_cp;
endgroup


covergroup misty_bits_cg(int i) with function sample(misty_seq_item_base trans);
    cp_0: coverpoint trans.text_i[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }

    cp_1: coverpoint trans.text_o[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
endgroup

covergroup misty_key_bits_cg(int i) with function sample(misty_seq_item_base trans);
    cp_0: coverpoint trans.key[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
endgroup

//---------------------------------------------------------
// Class: FO_cov
//---------------------------------------------------------


class misty_cov_wrapper extends uvm_object;


    `uvm_object_utils(misty_cov_wrapper)


    misty_bits_cg misty_bits_cg [63:0];
    misty_key_bits_cg misty_key_bits_cg [255:0];
    misty_value_cg misty_value_cg ; 


    function new(string name = "");
        super.new(name);
        misty_value_cg   = new();
        for(int i = 0; i < 64; i++) begin
            misty_bits_cg[i] = new(i);
        end
        for(int i = 0; i < 256; i++) begin
            misty_key_bits_cg[i] = new(i);
        end
    endfunction


    virtual function void sample(misty_seq_item_base t);
            misty_value_cg.sample(t);
            for(int i = 0; i < 64; i++) begin
                misty_bits_cg[i].sample(t);
            end
            for(int i = 0; i < 256; i++) begin
                misty_key_bits_cg[i].sample(t);
            end            
    endfunction

endclass