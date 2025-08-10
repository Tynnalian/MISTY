//---------------------------------------------------------
// Covergroups for functional coverage
//---------------------------------------------------------

// Checking data from input and output transaction

covergroup KS_value_cg with function sample(KS_seq_item_base trans);

    key_cp: coverpoint trans.key {
        bins b1 [250] = {[0:$]};
    }
    exp_key_cp: coverpoint trans.expand_keys {
        bins b1 [500] = {[0:$]};
    }

endgroup


covergroup key_bits_cg(int i) with function sample(KS_seq_item_base trans);

    cp_0: coverpoint trans.key[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }

endgroup


covergroup exp_key_bits_cg(int i) with function sample(KS_seq_item_base trans);

    cp_0: coverpoint trans.expand_keys[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }

endgroup



//---------------------------------------------------------
// Class: KS_cov
//---------------------------------------------------------


class KS_cov_wrapper extends uvm_object;


    `uvm_object_utils(KS_cov_wrapper)


    key_bits_cg key_bits_cg [127:0];
    exp_key_bits_cg exp_key_bits_cg [255:0];

    KS_value_cg KS_value_cg ; 


    function new(string name = "");
        super.new(name);
        KS_value_cg   = new();
        for(int i = 0; i < 128; i++) begin
            key_bits_cg[i] = new(i);
        end
        for(int i = 0; i < 256; i++) begin
            exp_key_bits_cg[i] = new(i);
        end
    endfunction


    virtual function void sample(KS_seq_item_base t);
            KS_value_cg.sample(t);
            for(int i = 0; i < 128; i++) begin
                key_bits_cg[i].sample(t);
            end
            for(int i = 0; i < 256; i++) begin
                exp_key_bits_cg[i].sample(t);
            end
    endfunction

endclass
