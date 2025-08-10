//---------------------------------------------------------
// Covergroups for functional coverage
//---------------------------------------------------------

// Checking data from input and output transaction

covergroup FI_value_cg with function sample(FI_seq_item_base trans);

    plain_i_cp: coverpoint trans.plain {
        bins b1 [100] = {[0:$]};
    }
    key_cp: coverpoint trans.key {
        bins b1 [100] = {[0:$]};
    }
    sypher_o_cp: coverpoint trans.sypher {
        bins b1 [100] = {[0:$]};
    }
    plainXkey: cross plain_i_cp, key_cp;
endgroup


covergroup FI_bits_cg(int i) with function sample(FI_seq_item_base trans);
    cp_0: coverpoint trans.plain[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
    cp_1: coverpoint trans.key[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
    cp_2: coverpoint trans.sypher[i] {
        bins b1 = (0 => 1);
        bins b2 = (1 => 0);
    }
endgroup



//---------------------------------------------------------
// Class: FI_cov
//---------------------------------------------------------


class FI_cov_wrapper extends uvm_object;


    `uvm_object_utils(FI_cov_wrapper)


    FI_bits_cg FI_bits_cg [15:0];
    FI_value_cg FI_value_cg ; 


    function new(string name = "");
        super.new(name);
        FI_value_cg   = new();
        for(int i = 0; i < 16; i++) begin
            FI_bits_cg[i] = new(i);
        end
    endfunction


    virtual function void sample(FI_seq_item_base t);
            FI_value_cg.sample(t);
            for(int i = 0; i < 16; i++) begin
                FI_bits_cg[i].sample(t);
            end
    endfunction

endclass
