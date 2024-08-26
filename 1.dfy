// 定义常量  
const MAX_CSR_PMP: int := 63  
const PMP_SHIFT: int := 2  
const RISCV_XLEN: int := 64  
const CSR_PMPCFG0: int := 0x3A0  
const CSR_PMPADDR0: int := 0x3B0  
const EINVAL: int := 22  

// PMP 配置位  
const PMP_R: bv8 := 0x01 
const PMP_W: bv8 := 0x02 
const PMP_X: bv8 := 0x04 
const PMP_RWX: bv8 := 0x8
const PMP_A: bv8 := 0x18  
const PMP_L: bv8 := 0x80  
const PMP_A_NA4: bv8 := 0x10  
const PMP_A_NAPOT: bv8 := 0x18  

// 定义有效的 PMP 配置位掩码  
const VALID_PMP_FLAGS: bv8 := PMP_R | PMP_W | PMP_X | PMP_A | PMP_L  

// 定义 PMP 条目结构  
datatype PMPEntry = PMPEntry(addr: bv64, cfg: bv8)  

// 硬件状态  
class HardwareState {  
    var pmp_entries: seq<PMPEntry>;  

    constructor()  
        ensures |pmp_entries| == MAX_CSR_PMP + 1  
    {  
        pmp_entries := seq(MAX_CSR_PMP + 1, i => PMPEntry(0 as bv64, 0 as bv8));  
    }  
}  

// 辅助函数  
function is_power_of_two(n: bv64): bool  
{  
    n != 0 as bv64 && (n & (n - 1 as bv64)) == 0 as bv64  
}  

function log2roundup(size: bv64): int  
    requires 1 as bv64 <= size < 0x7FFFFFFFFFFFFFFF as bv64  
    ensures 0 <= log2roundup(size) < 64  
{  
   
    if size == 1 as bv64 then 0  
    else if size <= 2 as bv64 then 1  
    else if size <= 4 as bv64 then 2  
    else if size <= 8 as bv64 then 3  
    else if size <= 16 as bv64 then 4  
    else if size <= 32 as bv64 then 5  
    else if size <= 64 as bv64 then 6  
    else if size <= 128 as bv64 then 7  
    else 8  // 这里我们只处理到 2^7，你可以根据需要继续扩展  
}  


// 主方法  
method sbi_set_pmp(hw: HardwareState, reg_idx: int, start: bv64, size: bv64, prot: bv8) returns (r: int)  
    modifies hw  
    requires 1 as bv64 <= size <= 0xFFFFFFFFFFFFFFF as bv64  
    ensures r == 0 ==> (  
        0 <= reg_idx < |hw.pmp_entries| &&  var new_entry := hw.pmp_entries[reg_idx];  
        new_entry.cfg == ((prot & (0xff as bv8 - PMP_A)) | (if size == 4 as bv64 then PMP_A_NA4 else PMP_A_NAPOT)) &&  
        (size == 4 as bv64 ==> new_entry.addr == start >> PMP_SHIFT) &&  
        (size > 4 as bv64 ==>   
            (size == (1 as bv64 << 64) - 1 as bv64 && new_entry.addr == 0xffffffffffffffff as bv64) ||  
            (is_power_of_two(size) && new_entry.addr == ((start >> PMP_SHIFT) & ((0xffffffffffffffff as bv64 - (size >> PMP_SHIFT)) + 1 as bv64)) | ((size >> (PMP_SHIFT + 1)) - 1 as bv64))  
        )  
    )  
    ensures r != 0 ==> hw.pmp_entries == old(hw.pmp_entries)
    ensures r == 0 || r == 1 || r == -2  || r == -3  || r == -4  || r == -5  || r == -1    
{  

    if (reg_idx < 0 ) {  
        return -1;  
    }  
    if(0<size < 0xFFFFFFFFFFFFFFFF){
       return 1;}
    if(reg_idx > MAX_CSR_PMP ){
       return -3;
    }
   if(start + size < start ){
       return -4;
    }
    if((prot & VALID_PMP_FLAGS) != prot){
      return -5 ;
    }

    var order := log2roundup(size);  
    if (order < PMP_SHIFT) {  
        return -6;  
    }  
    var new_entry := hw.pmp_entries[reg_idx]; 
    // new_entry := PMPEntry();   
    var pmpaddr: bv64 := start >> PMP_SHIFT;  
    var pmpcfg: bv8 := prot & (0xff as bv8 - PMP_A);  

    if (order == PMP_SHIFT) {  
        pmpcfg := pmpcfg | PMP_A_NA4;  
    } else {  
        pmpcfg := pmpcfg | PMP_A_NAPOT;  
        if (order == RISCV_XLEN) {  
            pmpaddr := 0xffffffffffffffff as bv64;  
        } else {  
            var addrmask: bv64 := (1 as bv64 << (order - PMP_SHIFT)) - 1 as bv64;  
            pmpaddr := (pmpaddr & (0xffffffffffffffff as bv64 - addrmask)) | (addrmask >> 1);  
        }  
    }  

    hw.pmp_entries := hw.pmp_entries[reg_idx := PMPEntry(pmpaddr, pmpcfg)];  

    return 0;  
}  
// 测试方法  
  
 // 测试方法  
method Main()  
{  
    var hw := new HardwareState();  
    
    var MAX_U64: bv64 := 0xFFFFFFFFFFFFFFF as bv64 ; 
    var result0 := sbi_set_pmp(hw, 1, 0x80000000 as bv64, 0x40000 as bv64, PMP_RWX); 
    print result0;
    var result := sbi_set_pmp(hw, 0, 0, MAX_U64, PMP_RWX);
    print result; 
    var r3 := sbi_set_pmp(hw, 2, 0xF0000000 as bv64, 2 as bv64, PMP_R);  
    print r3; 
    var r4 := sbi_set_pmp(hw, 3, 0x3000 as bv64, 0x1000 as bv64, 0xff as bv8);  
    print r4; 

}  