//---------------------------------------------------------
// Covergroups for functional coverage
//---------------------------------------------------------

// Checking data from input and output transaction

covergroup FO_value_cg with function sample(FO_seq_item_base trans);

    plain_i_cp: coverpoint trans.plain {
        bins b1 [250] = {[0:$]};
    }
    key_I_cp: coverpoint trans.key_I {
        bins b1 [250] = {[0:$]};
    }
    key_O_cp: coverpoint trans.key_O {
        bins b1 [250] = {[0:$]};
    }

    plain_small_i_cp: coverpoint trans.plain {
        bins b1 [20] = {[0:$]};
    }
    key_small_I_cp: coverpoint trans.key_I {
        bins b1 [20] = {[0:$]};
    }
    key_small_O_cp: coverpoint trans.key_O {
        bins b1 [20] = {[0:$]};
    }
    sypher_o_cp: coverpoint trans.sypher {
        bins b1 [250] = {[0:$]};
    }
    plainXkey: cross plain_small_i_cp, key_small_I_cp, key_small_O_cp;
endgroup


covergroup FO_bits_cg(int i) with function sample(FO_seq_item_base trans);
    cp_0: coverpoint trans.plain[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }

    cp_1: coverpoint trans.sypher[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
endgroup

covergroup FO_KEY_I_bits_cg(int i) with function sample(FO_seq_item_base trans);
    cp_0: coverpoint trans.key_I[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
endgroup

covergroup FO_KEY_O_bits_cg(int i) with function sample(FO_seq_item_base trans);
    cp_0: coverpoint trans.key_O[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
endgroup



//---------------------------------------------------------
// Class: FO_cov
//---------------------------------------------------------


class FO_cov_wrapper extends uvm_object;


    `uvm_object_utils(FO_cov_wrapper)


    FO_bits_cg FO_bits_cg [31:0];
    FO_KEY_I_bits_cg FO_KEY_I_bits_cg [47:0];
    FO_KEY_O_bits_cg FO_KEY_O_bits_cg [63:0];
    FO_value_cg FO_value_cg ; 


    function new(string name = "");
        super.new(name);
        FO_value_cg   = new();
        for(int i = 0; i < 32; i++) begin
            FO_bits_cg[i] = new(i);
        end
        for(int i = 0; i < 48; i++) begin
            FO_KEY_I_bits_cg[i] = new(i);
        end
        for(int i = 0; i < 64; i++) begin
            FO_KEY_O_bits_cg[i] = new(i);
        end
    endfunction


    virtual function void sample(FO_seq_item_base t);
            FO_value_cg.sample(t);
            for(int i = 0; i < 32; i++) begin
                FO_bits_cg[i].sample(t);
            end
            for(int i = 0; i < 48; i++) begin
                FO_KEY_I_bits_cg[i].sample(t);
            end
            for(int i = 0; i < 64; i++) begin
                FO_KEY_O_bits_cg[i].sample(t);
            end
    endfunction

endclass
