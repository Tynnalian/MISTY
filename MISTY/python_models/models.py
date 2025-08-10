from pysv import sv, compile_lib, generate_sv_binding
from pysv import DataType
import binop
import S7
import S9
import FI
import FL
import FO
import ks
import FL_reverse
import misty1




class FI_model:
    def __init__(self):
        self.__KI_L = []
        self.__KI_R = []
        self.__plainA = []
        self.__sypherA = []

    #Fuctions for filling arrays

    @sv(data=DataType.UInt)
    def fill_KI_L(self, data):
        self.__KI_L.append(data)

    @sv(data=DataType.UInt)
    def fill_KI_R(self, data):
        self.__KI_R.append(data)

    @sv(data=DataType.UInt)
    def fill_plainA(self, data):
        self.__plainA.append(data)        

    @sv()
    def FI(self):
        KI_L = self.__KI_L
        KI_R = self.__KI_R
        plainA = self.__plainA
        self.__sypherA = FI.FI(KI_L,KI_R,plainA)

    @sv()
    def delete_array(self):
        self.__KI_L = []
        self.__KI_R = []
        self.__plainA = []
        self.__sypherA = []

    @sv()
    def size(self):
        return len(self.__array)
    
    @sv(idx=DataType.UInt, return_type=DataType.UInt)
    def get(self, idx):
        return self.__sypherA[len(self.__sypherA)-1-idx]


class FO_model:
    def __init__(self):
        self.__KI_mas = []
        self.__KO_mas = []
        self.__plainA = []
        self.__sypherA = []

    #Fuctions for filling arrays

    @sv(data=DataType.UInt)
    def fill_KI_mas(self, data):
        self.__KI_mas.append(data)

    @sv(data=DataType.UInt)
    def fill_KO_mas(self, data):
        self.__KO_mas.append(data)

    @sv(data=DataType.UInt)
    def fill_plainA(self, data):
        self.__plainA.append(data)        

    @sv()
    def FO(self):
        KI_mas = [self.__KI_mas[i:i + 16] for i in range(0, 48, 16)]  
        KO_mas = [self.__KO_mas[i:i + 16] for i in range(0, 64, 16)]
        plainA = self.__plainA  
        self.__sypherA = FO.FO(KI_mas,KO_mas,plainA)
    
    @sv()
    def delete_array(self):
        self.__KI_mas = []
        self.__KO_mas = []
        self.__plainA = []
        self.__sypherA = []

    @sv()
    def size(self):
        return len(self.__array)
    
    @sv(idx=DataType.UInt, return_type=DataType.UInt)
    def get(self, idx):
        return self.__sypherA[len(self.__sypherA)-1-idx]

class KS_model:
    def __init__(self):
        self.__K = []
        self.__KE= []

    #Fuctions for filling arrays

    @sv(data=DataType.UInt)
    def fill_K(self, data):
        self.__K.append(data)

           

    @sv()
    def key_schedule(self):
        K=self.__K
        K_o=ks.key_schedule(K)
        self.__KE = [item for sublist in K_o for item in sublist]


    @sv()
    def delete_array(self):
        self.__K = []
        self.__KE= []

    @sv()
    def size(self):
        return len(self.__KE)
    
    @sv(idx=DataType.UInt, return_type=DataType.UInt)
    def get(self, idx):
        return self.__KE[len(self.__KE)-1-idx]

class MISTY_model:
    def __init__(self):
        self.__plainA = []
        self.__exp_key = []
        self.__sypherA = []
        self.__syph_i = []
    #Fuctions for filling arrays

    @sv(data=DataType.UInt)
    def fill_plainA(self, data):
        self.__plainA.append(data)

    @sv(data=DataType.UInt)
    def fill_exp_key(self, data):
        self.__exp_key.append(data)

    @sv(data=DataType.UInt)
    def fill_sypher(self, data):
        self.__syph_i.append(data)        

    @sv()
    def Encryption_Mode(self):
        exp_key = [self.__exp_key[i:i + 16] for i in range(0, len(self.__exp_key), 16)]
        plainA =  self.__plainA
        self.__sypherA = misty1.Encryption_Mode(plainA,exp_key)
    

    @sv()
    def Decryption_Mode(self):
        exp_key = [self.__exp_key[i:i + 16] for i in range(0, len(self.__exp_key), 16)]
        sypherA = self.__syph_i
        self.__plainA = misty1.Decryption_Mode(sypherA,exp_key)


    @sv()
    def size(self):
        return len(self.__sypherA)
    
    @sv(idx=DataType.UInt, return_type=DataType.UInt)
    def get_sypher(self, idx):
        return self.__sypherA[len(self.__sypherA)-1-idx]

    @sv(idx=DataType.UInt, return_type=DataType.UInt)
    def get_plain(self, idx):
        return self.__plainA[len(self.__plainA)-1-idx]

    @sv()
    def delete_array(self):
        self.__plainA = []
        self.__exp_key = []
        self.__sypherA = []
        self.__syph_i = []





lib_path = compile_lib([FI_model,FO_model,KS_model,MISTY_model], cwd="build")

generate_sv_binding([FI_model,FO_model,KS_model,MISTY_model], filename="pysv_pkg.sv")