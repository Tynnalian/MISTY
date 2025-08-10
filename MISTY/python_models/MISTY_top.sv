`timescale 1ns/1ps

module MISTY_top();
    // import from the pysv package
    import pysv::*;


    initial begin
        //---------------------------------------------------------
        // Testing programm
        //---------------------------------------------------------
        logic [63:0]  plain;
        logic [255:0] key;
        logic [63:0]  sypher; 
 

        automatic MISTY_model model = new();
        // automatic int int_arr [] ;
        // try = 8'b10101011;

        // keyL = 7'b0101010;
        
        
        // $display("%p", int_arr);
        // int_arr.delete();
        // $display("%p", int_arr);
        // int_arr = new[model.size()];
        key = 256'h00112233445566778899aabbccddeeffcf518e7f5e29673acdbc07d6bf355e11;
        plain = 64'h0123456789abcdef;

        $display("plain %h",plain);
        


        foreach (plain[i]) begin
            model.fill_plainA(int'(plain[i]));
        end

        foreach (key[i]) begin
            model.fill_exp_key(int'(key[i]));
        end

        model.Encryption_Mode();

        foreach (sypher[i]) begin
            sypher[i] = model.get_sypher(i);
        end


        $display("sypher %b",sypher);
        $display("sypher %h",sypher);

        foreach (sypher[i]) begin
            model.fill_sypher(int'(sypher[i]));
        end

        foreach (key[i]) begin
            model.fill_exp_key(int'(key[i]));
        end

        model.Decryption_Mode();
        
        plain = 0;
        $display("plain %b",plain);

        foreach (plain[i]) begin
            plain[i] = model.get_plain(i);
        end


        $display("plain %h",plain);

        pysv_finalize(); 
    end
endmodule    