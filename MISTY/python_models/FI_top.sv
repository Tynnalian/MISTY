`timescale 1ns/1ps

module FI_top();
    // import from the pysv package
    import pysv::*;


    initial begin
        //---------------------------------------------------------
        // Testing programm
        //---------------------------------------------------------
        logic [8:0] keyR;
        logic [6:0] keyL; 
        logic [15:0] plain;
        logic [15:0] sypher; 

        automatic FI_model model = new();
        // automatic int int_arr [] ;
        // try = 8'b10101011;

        // keyL = 7'b0101010;
        
        
        // $display("%p", int_arr);
        // int_arr.delete();
        // $display("%p", int_arr);
        // int_arr = new[model.size()];
        keyL = 7'b0101010;
        keyR = 9'b010101011;
        plain = 16'b0010101001010111;

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
        
        $display("sypher %b",sypher);
        pysv_finalize(); 
    end

endmodule