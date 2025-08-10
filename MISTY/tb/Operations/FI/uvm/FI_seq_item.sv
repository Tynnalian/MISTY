//---------------------------------------------------------
// Class: FI_seq_item_base
//---------------------------------------------------------
//
// FI base sequence item

class FI_seq_item_base extends uvm_sequence_item;
    `uvm_object_utils(FI_seq_item_base)


    rand logic [16 - 1: 0] plain;

    rand logic [16 - 1: 0] key;

    rand logic [16 - 1: 0] sypher;

  

    function new(string name = "");
        super.new(name);  
    endfunction

    //---------------------------------------------------------
    // Function: do_copy
    //---------------------------------------------------------
    
    // Copy function for the FI sequence item

    virtual function void do_copy(uvm_object rhs);
        FI_seq_item_base that;
        if( !$cast(that, rhs) ) begin
            `uvm_fatal(get_name(),
                $sformatf("rhs is not 'FI_seq_item_base' type"));
        end
        super.do_copy(that); 
        this.plain = that.plain; 
        this.key = that.key;
        this.sypher = that.sypher;    
    endfunction

    //---------------------------------------------------------
    // Function: convert2string
    //---------------------------------------------------------
    
    // Convert the FI sequence item to string format
    
    virtual function string convert2string();
        string str;
        str = {str, $sformatf("\ntdata: %8h",   plain)}; 
        str = {str, $sformatf("\ntdata: %8h",   key)};  
        str = {str, $sformatf("\ntid  : %8h",   sypher  )};   
        return str;  
    endfunction

endclass
