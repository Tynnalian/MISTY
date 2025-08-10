`ifndef PYSV_PYSV
`define PYSV_PYSV
package pysv;
import "DPI-C" function void FI_model_FI(input chandle self);
import "DPI-C" function chandle FI_model_pysv_init();
import "DPI-C" function void FI_model_delete_array(input chandle self);
import "DPI-C" function void FI_model_destroy(input chandle self);
import "DPI-C" function void FI_model_fill_KI_L(input chandle self,
                                                input int unsigned data);
import "DPI-C" function void FI_model_fill_KI_R(input chandle self,
                                                input int unsigned data);
import "DPI-C" function void FI_model_fill_plainA(input chandle self,
                                                  input int unsigned data);
import "DPI-C" function int unsigned FI_model_get(input chandle self,
                                                  input int unsigned idx);
import "DPI-C" function int FI_model_size(input chandle self);
import "DPI-C" function void FO_model_FO(input chandle self);
import "DPI-C" function chandle FO_model_pysv_init();
import "DPI-C" function void FO_model_delete_array(input chandle self);
import "DPI-C" function void FO_model_destroy(input chandle self);
import "DPI-C" function void FO_model_fill_KI_mas(input chandle self,
                                                  input int unsigned data);
import "DPI-C" function void FO_model_fill_KO_mas(input chandle self,
                                                  input int unsigned data);
import "DPI-C" function void FO_model_fill_plainA(input chandle self,
                                                  input int unsigned data);
import "DPI-C" function int unsigned FO_model_get(input chandle self,
                                                  input int unsigned idx);
import "DPI-C" function int FO_model_size(input chandle self);
import "DPI-C" function chandle KS_model_pysv_init();
import "DPI-C" function void KS_model_delete_array(input chandle self);
import "DPI-C" function void KS_model_destroy(input chandle self);
import "DPI-C" function void KS_model_fill_K(input chandle self,
                                             input int unsigned data);
import "DPI-C" function int unsigned KS_model_get(input chandle self,
                                                  input int unsigned idx);
import "DPI-C" function void KS_model_key_schedule(input chandle self);
import "DPI-C" function int KS_model_size(input chandle self);
import "DPI-C" function void MISTY_model_Decryption_Mode(input chandle self);
import "DPI-C" function void MISTY_model_Encryption_Mode(input chandle self);
import "DPI-C" function chandle MISTY_model_pysv_init();
import "DPI-C" function void MISTY_model_delete_array(input chandle self);
import "DPI-C" function void MISTY_model_destroy(input chandle self);
import "DPI-C" function void MISTY_model_fill_exp_key(input chandle self,
                                                      input int unsigned data);
import "DPI-C" function void MISTY_model_fill_plainA(input chandle self,
                                                     input int unsigned data);
import "DPI-C" function void MISTY_model_fill_sypher(input chandle self,
                                                     input int unsigned data);
import "DPI-C" function int unsigned MISTY_model_get_plain(input chandle self,
                                                           input int unsigned idx);
import "DPI-C" function int unsigned MISTY_model_get_sypher(input chandle self,
                                                            input int unsigned idx);
import "DPI-C" function int MISTY_model_size(input chandle self);
import "DPI-C" function void pysv_finalize();
class PySVObject;
chandle pysv_ptr;
endclass
class FI_model extends PySVObject;
  function void FI();
    FI_model_FI(pysv_ptr);
  endfunction
  function new();
    pysv_ptr = FI_model_pysv_init();
  endfunction
  function void delete_array();
    FI_model_delete_array(pysv_ptr);
  endfunction
  function void destroy();
    FI_model_destroy(pysv_ptr);
  endfunction
  function void fill_KI_L(input int unsigned data);
    FI_model_fill_KI_L(pysv_ptr, data);
  endfunction
  function void fill_KI_R(input int unsigned data);
    FI_model_fill_KI_R(pysv_ptr, data);
  endfunction
  function void fill_plainA(input int unsigned data);
    FI_model_fill_plainA(pysv_ptr, data);
  endfunction
  function int unsigned get(input int unsigned idx);
    return FI_model_get(pysv_ptr, idx);
  endfunction
  function int size();
    return FI_model_size(pysv_ptr);
  endfunction
endclass
class FO_model extends PySVObject;
  function void FO();
    FO_model_FO(pysv_ptr);
  endfunction
  function new();
    pysv_ptr = FO_model_pysv_init();
  endfunction
  function void delete_array();
    FO_model_delete_array(pysv_ptr);
  endfunction
  function void destroy();
    FO_model_destroy(pysv_ptr);
  endfunction
  function void fill_KI_mas(input int unsigned data);
    FO_model_fill_KI_mas(pysv_ptr, data);
  endfunction
  function void fill_KO_mas(input int unsigned data);
    FO_model_fill_KO_mas(pysv_ptr, data);
  endfunction
  function void fill_plainA(input int unsigned data);
    FO_model_fill_plainA(pysv_ptr, data);
  endfunction
  function int unsigned get(input int unsigned idx);
    return FO_model_get(pysv_ptr, idx);
  endfunction
  function int size();
    return FO_model_size(pysv_ptr);
  endfunction
endclass
class KS_model extends PySVObject;
  function new();
    pysv_ptr = KS_model_pysv_init();
  endfunction
  function void delete_array();
    KS_model_delete_array(pysv_ptr);
  endfunction
  function void destroy();
    KS_model_destroy(pysv_ptr);
  endfunction
  function void fill_K(input int unsigned data);
    KS_model_fill_K(pysv_ptr, data);
  endfunction
  function int unsigned get(input int unsigned idx);
    return KS_model_get(pysv_ptr, idx);
  endfunction
  function void key_schedule();
    KS_model_key_schedule(pysv_ptr);
  endfunction
  function int size();
    return KS_model_size(pysv_ptr);
  endfunction
endclass
class MISTY_model extends PySVObject;
  function void Decryption_Mode();
    MISTY_model_Decryption_Mode(pysv_ptr);
  endfunction
  function void Encryption_Mode();
    MISTY_model_Encryption_Mode(pysv_ptr);
  endfunction
  function new();
    pysv_ptr = MISTY_model_pysv_init();
  endfunction
  function void delete_array();
    MISTY_model_delete_array(pysv_ptr);
  endfunction
  function void destroy();
    MISTY_model_destroy(pysv_ptr);
  endfunction
  function void fill_exp_key(input int unsigned data);
    MISTY_model_fill_exp_key(pysv_ptr, data);
  endfunction
  function void fill_plainA(input int unsigned data);
    MISTY_model_fill_plainA(pysv_ptr, data);
  endfunction
  function void fill_sypher(input int unsigned data);
    MISTY_model_fill_sypher(pysv_ptr, data);
  endfunction
  function int unsigned get_plain(input int unsigned idx);
    return MISTY_model_get_plain(pysv_ptr, idx);
  endfunction
  function int unsigned get_sypher(input int unsigned idx);
    return MISTY_model_get_sypher(pysv_ptr, idx);
  endfunction
  function int size();
    return MISTY_model_size(pysv_ptr);
  endfunction
endclass
endpackage
`endif // PYSV_PYSV
