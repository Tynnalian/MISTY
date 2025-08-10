`timescale 1ns/1ps

module FO_top();
    // import from the pysv package
    import pysv::*;


    initial begin
        //---------------------------------------------------------
        // Testing programm
        //---------------------------------------------------------
        logic [47:0] key_i;
        logic [63:0] key_o; 
        logic [31:0] plain;
        logic [31:0] sypher; 

        automatic FO_model model = new();
        // automatic int int_arr [] ;
        // try = 8'b10101011;

        // keyL = 7'b0101010;
        
        
        // $display("%p", int_arr);
        // int_arr.delete();
        // $display("%p", int_arr);
        // int_arr = new[model.size()];
        key_i = $urandom();
        key_o =  $urandom();
        plain = $urandom();

        foreach (key_i[i]) begin
            model.fill_KI_mas(int'(key_i[i]));
        end
        foreach (key_o[i]) begin
            model.fill_KO_mas(int'(key_o[i]));
        end
        foreach (plain[i]) begin
            model.fill_plainA(int'(plain[i]));
        end

        model.FO();

        foreach (sypher[i]) begin
            sypher[i] = model.get(i);
        end
        
        $display("sypher %b",sypher);
        pysv_finalize(); 
    end

endmodule