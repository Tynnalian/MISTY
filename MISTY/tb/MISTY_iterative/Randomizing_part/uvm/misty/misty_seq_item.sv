//---------------------------------------------------------
// Class: misty_seq_item
//---------------------------------------------------------

// misty base sequence item.

class misty_seq_item_base extends uvm_sequence_item;

    `uvm_object_utils(misty_seq_item_base)

    rand logic         enc;
    rand logic [63:0]  text_i;
    rand logic [255:0] key;
    rand logic [63:0]  text_o;
    logic              valid_i;
    logic              valid_o;


    // Constructor.

    function new(string name = "");
        super.new(name);
    endfunction

    // Avoid of using uvm_field_*. Use do-hooks instead.

    virtual function void do_copy(uvm_object rhs);
        misty_seq_item_base that;
        if( !$cast(that, rhs) ) begin
            `uvm_fatal(get_name(),
                $sformatf("rhs is not 'misty_seq_item_base' type"));
        end
        super.do_copy(that);
        this.enc    = that.enc;
        this.text_i = that.text_i;
        this.text_o = that.text_o;
        this.key    = that.key;
        this.valid_i    = that.valid_i;
        this.valid_o    = that.valid_o;
    endfunction

    virtual function string convert2string();
        string str;
        str = {str, $sformatf("\n-------%s-------", get_type_name())};
        str = {str, $sformatf("\ntext_i: %h", text_i)};
        str = {str, $sformatf("\nkey  :  %h", key  )};
        str = {str, $sformatf("\ntext_o: %h", text_o)};
        str = {str, $sformatf("\nenc  :  %h", enc  )};
        str = {str, $sformatf("\nvalid_i  :  %h", valid_i  )};
        str = {str, $sformatf("\nvalid_o  :  %h", valid_o  )};
        str = {str, $sformatf("\n-------%s-------", {get_type_name().len(){"-"}})};
        return str;
    endfunction

endclass
