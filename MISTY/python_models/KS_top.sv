`timescale 1ns/1ps

module KS_top();
    // import from the pysv package
    import pysv::*;


    initial begin
        //---------------------------------------------------------
        // Testing programm
        //---------------------------------------------------------
        logic [127:0] key_i;
        logic [255:0] key_o; 
 

        automatic KS_model model = new();
        // automatic int int_arr [] ;
        // try = 8'b10101011;

        // keyL = 7'b0101010;
        
        
        // $display("%p", int_arr);
        // int_arr.delete();
        // $display("%p", int_arr);
        // int_arr = new[model.size()];
        key_i = 128'h00112233445566778899aabbccddeeff;


        foreach (key_i[i]) begin
            model.fill_K(int'(key_i[i]));
        end

        model.key_schedule();

        foreach (key_o[i]) begin
            key_o[i] = model.get(i);
        end
        
        $display("key_o %h",key_o);
        $display("len %d",model.size());
        pysv_finalize(); 
    end

endmodule