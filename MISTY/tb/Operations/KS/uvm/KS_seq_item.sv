//---------------------------------------------------------
// Class: KS_seq_item_base
//---------------------------------------------------------
//
// KS base sequence item

class KS_seq_item_base extends uvm_sequence_item;
    `uvm_object_utils(KS_seq_item_base)

    rand logic [128 - 1: 0] key;

        logic [256 - 1: 0] expand_keys;

  

    function new(string name = "");
        super.new(name);  
    endfunction

    //---------------------------------------------------------
    // Function: do_copy
    //---------------------------------------------------------
    
    // Copy function for the KS sequence item

    virtual function void do_copy(uvm_object rhs);
        KS_seq_item_base that;
        if( !$cast(that, rhs) ) begin
            `uvm_fatal(get_name(),
                $sformatf("rhs is not 'KS_seq_item_base' type"));
        end
        super.do_copy(that); 
        this.key = that.key;
        this.expand_keys = that.expand_keys;    
    endfunction

    //---------------------------------------------------------
    // Function: convert2string
    //---------------------------------------------------------
    
    // Convert the KS sequence item to string format
    
    virtual function string convert2string();
        string str;
        str = {str, $sformatf("\nkey: %8h",   key)};  
        str = {str, $sformatf("\nexpand_keys  : %8h",   expand_keys  )};   
        return str;  
    endfunction

endclass
