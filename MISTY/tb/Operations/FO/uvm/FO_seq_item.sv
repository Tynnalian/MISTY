//---------------------------------------------------------
// Class: FO_seq_item_base
//---------------------------------------------------------
//
// FO base sequence item

class FO_seq_item_base extends uvm_sequence_item;
    `uvm_object_utils(FO_seq_item_base)


    rand logic [32 - 1: 0] plain;

    rand logic [48 - 1: 0] key_I;

    rand logic [64 - 1: 0] key_O;

    rand logic [32 - 1: 0] sypher;

  

    function new(string name = "");
        super.new(name);  
    endfunction

    //---------------------------------------------------------
    // Function: do_copy
    //---------------------------------------------------------
    
    // Copy function for the FO sequence item

    virtual function void do_copy(uvm_object rhs);
        FO_seq_item_base that;
        if( !$cast(that, rhs) ) begin
            `uvm_fatal(get_name(),
                $sformatf("rhs is not 'FO_seq_item_base' type"));
        end
        super.do_copy(that); 
        this.plain = that.plain; 
        this.key_I= that.key_I;
        this.key_O= that.key_O;
        this.sypher = that.sypher;    
    endfunction

    //---------------------------------------------------------
    // Function: convert2string
    //---------------------------------------------------------
    
    // Convert the FO sequence item to string format
    
    virtual function string convert2string();
        string str;
        str = {str, $sformatf("\ntdata: %8h",   plain)}; 
        str = {str, $sformatf("\ntdata: %8h",   key_I)};
        str = {str, $sformatf("\ntdata: %8h",   key_O)};  
        str = {str, $sformatf("\ntdata  : %8h",   sypher  )};   
        return str;  
    endfunction

endclass
