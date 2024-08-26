// 常量定义  
const BANNER: string;  
const PRV_S: bv32;  
const MSTATUS_MPP: bv32;
const MSTATUS_MPIE: bv32;
// 常量定义  
const MAX_CSR_PMP: int := 16;  // 假设最大PMP条目数为16  
const PMP_SHIFT: int := 2;  
const RISCV_XLEN: int := 64;  // 假设是64位RISC-V  
const PMP_RWX: int := 7;  // Read (1) + Write (2) + Execute (4)  
const FW_JUMP_ADDR: bv32 := 0x80200000;  

// 模拟CSR寄存器  
class CSRState {  
  var mstatus: bv32;  
  var mepc: bv32;  
  var stvec: bv32;  
  var sie: bv32;  
  var satp: bv32;  
  var pmpcfg: array<int>;  
  var pmpaddr: array<int>;  

  constructor()  
    ensures fresh(pmpcfg) && fresh(pmpaddr)  
    ensures pmpcfg.Length == MAX_CSR_PMP / 4  
    ensures pmpaddr.Length == MAX_CSR_PMP  
  {  
    pmpcfg := new int[MAX_CSR_PMP / 4];  
    pmpaddr := new int[MAX_CSR_PMP];  
  }  
}  

class SystemState{ 
  var csrs: CSRState  
  var currentMode: int  // 0: U-mode, 1: S-mode, 3: M-mode  

  constructor()  
    ensures fresh(csrs)  
    ensures currentMode == 3  // 初始为M-mode  
  {  
    csrs := new CSRState();  
    currentMode := 3;  
  }  
} 

// 辅助方法  
method uart_init()  
method init_printk_done(f: char -> ())  
method printk(s: string)  
method sbi_trap_init()  
method check_h_extension() returns (b: bool)  
method delegate_traps()  

// 模拟CSR操作的方法  

method read_csr(reg: CSRState, csr_name: string) returns (value: bv32)  
{  
  match csr_name  
  {  
    case "mstatus" => return reg.mstatus;  
    case "mepc" => return reg.mepc;  
    // 其他 CSR ...  
    case default => return 0; // 或者抛出错误  
  }  
}  

method write_csr(regs: CSRState, csr_name: string, value: bv32) returns (updated_regs: CSRState)  
{  
  // 创建一个新的 CSRState 对象来存储更新后的状态  
  updated_regs := new CSRState();  
  
  // 复制所有现有的值  
  updated_regs.mstatus := regs.mstatus;  
  updated_regs.mepc := regs.mepc;  
  // ... 复制其他 CSR 值 ...  

  // 根据 csr_name 更新相应的寄存器  
  match csr_name  
  {  
    case "mstatus" => updated_regs.mstatus := value;  
    case "mepc" => updated_regs.mepc := value;  
    // ... 其他 CSR ...  
    case _ => // 如果是未知的 CSR，可以选择不做任何事，或者抛出错误  
  }  
}  
// 模拟PMP设置  
method sbi_set_pmp(index: int, start: int, size: int, prot: int)  
method init_print()
// 主方法  
method sbi_main()     
{  
  var val: bv32;  
  uart_init(); 
  init_print();  
  printk(BANNER); 
  sbi_trap_init();  
  sbi_set_pmp(0, 0, -1, PMP_RWX);  
  sbi_set_pmp(1, 0x80000000, 0x40000, PMP_RWX); 
  var h_extension := check_h_extension();  
  if h_extension {  
    printk("H extension implemented\n");  
  } else {  
    printk("H extension not implemented\n");  
  }  
  var sys := new SystemState(); 
  val := read_csr(sys.csrs, "mstatus");  
  val := INSERT_FIELD(val , MSTATUS_MPP , PRV_S); 
  val := INSERT_FIELD(val , MSTATUS_MPIE , PRV_S); 
  sys.csrs :=  write_csr(sys.csrs, "mstatus", val); 
  delegate_traps();  
  sys.csrs := write_csr(sys.csrs,"mepc", FW_JUMP_ADDR);  
  sys.csrs :=write_csr(sys.csrs,"stvec", FW_JUMP_ADDR);  
  sys.csrs :=write_csr(sys.csrs,"sie", 0);  
  sys.csrs :=write_csr(sys.csrs,"satp", 0);  
  sys := switch_to_s_mode(sys); 
}  
method switch_to_s_mode(sys: SystemState) returns (updated_sys: SystemState) 
function bitnot32(x: bv32): bv32  
{  
  !x as bv32  
}  
function INSERT_FIELD(val: bv32, which: bv32, fieldval: bv32): bv32 
{  
 (val & bitnot32(which)) | (fieldval & which)
}  
predicate fieldval_in_range(fieldval: bv32, which: bv32)  
{  
  (fieldval & bitnot32(which)) == 0   // 确保 fieldval 不超过 which 定义的范围  
}  

// 辅助引理1：A & !B | C & B 的 which 部分等于 C & B  
lemma InsertFieldWhichPart(val: bv32, which: bv32, fieldval: bv32)  
  ensures ((val & bitnot32(which)) | (fieldval & which)) & which == fieldval & which  
{  
  // Dafny 应该能自动证明这个基本性质  
}  

// 辅助引理2：A & !B | C & B 的非 which 部分等于 A & !B  
lemma InsertFieldNotWhichPart(A: bv32, B: bv32, C: bv32)  
  ensures ((A & bitnot32(B)) | (C & B)) & bitnot32(B) == A & bitnot32(B)  
{  
  // Dafny 应该能自动证明这个基本性质  
} 

lemma ProveUnchangedBits(val: bv32, which: bv32, fieldval: bv32)  
  ensures ((val & bitnot32(which)) | (fieldval & which)) & bitnot32(which)  
        == val & bitnot32(which)  
{  
  calc {  
    ((val & bitnot32(which)) | (fieldval & which)) & bitnot32(which);  
    == // 分配律  
    (val & bitnot32(which) & bitnot32(which)) | (fieldval & which & bitnot32(which));  
    == // A & A = A  
    (val & bitnot32(which)) | (fieldval & which & bitnot32(which));  
    == // A & !A = 0  
    (val & bitnot32(which)) | 0;  
    == // A | 0 = A  
    val & bitnot32(which);  
  }  
}

// 性质1：which 覆盖的位来自 fieldval  
lemma INSERT_FIELD_Property1(val: bv32, which: bv32, fieldval: bv32)  
  requires fieldval & which == fieldval  
  ensures INSERT_FIELD(val, which, fieldval) & which == fieldval  
{  
  calc {  
    INSERT_FIELD(val, which, fieldval) & which;  
    == // 展开 INSERT_FIELD 的定义  
    ((val & bitnot32(which)) | (fieldval & which)) & which;  
    == // 位运算的分配律  
    (val & bitnot32(which) & which) | (fieldval & which & which);  
    == // A & !A == 0, A & A == A  
    0 | (fieldval & which);  
    == // 0 | A == A  
    fieldval & which;  
    == // 根据前提条件  
    fieldval;  
  }  
}  

// 性质2：未被 which 覆盖的位保持不变  
lemma INSERT_FIELD_Property2(val: bv32, which: bv32, fieldval: bv32)  
  ensures INSERT_FIELD(val, which, fieldval) & bitnot32(which) == val & bitnot32(which)  
{  
  calc {  
    INSERT_FIELD(val, which, fieldval) & bitnot32(which);  
    == // 展开 INSERT_FIELD 的定义  
    ((val & bitnot32(which)) | (fieldval & which)) & bitnot32(which);  
    == // 位运算的分配律  
    (val & bitnot32(which) & bitnot32(which)) | (fieldval & which & bitnot32(which));  
    == // A & A == A, A & !A == 0  
    (val & bitnot32(which)) | 0;  
    == // A | 0 == A  
    val & bitnot32(which);  
  }  
}  


// 性质3：结果是预期的组合  
lemma INSERT_FIELD_Property3(val: bv32, which: bv32, fieldval: bv32)  
  requires fieldval & which == fieldval  
  ensures INSERT_FIELD(val, which, fieldval) == ((val & bitnot32(which)) | fieldval)  
{  
  calc {  
    INSERT_FIELD(val, which, fieldval);  
    == // INSERT_FIELD 的定义  
    (val & bitnot32(which)) | (fieldval & which);  
    == // 根据前提条件 fieldval & which == fieldval  
    (val & bitnot32(which)) | fieldval;  
  }  
}  

// 综合所有性质的引理  
lemma INSERT_FIELD_AllProperties(val: bv32, which: bv32, fieldval: bv32)  
  requires fieldval & which == fieldval  
  ensures INSERT_FIELD(val, which, fieldval) & which == fieldval  
  ensures INSERT_FIELD(val, which, fieldval) & bitnot32(which) == val & bitnot32(which)  
  ensures INSERT_FIELD(val, which, fieldval) == ((val & bitnot32(which)) | fieldval)  
{  
  INSERT_FIELD_Property1(val, which, fieldval);  
  INSERT_FIELD_Property2(val, which, fieldval);  
  INSERT_FIELD_Property3(val, which, fieldval);  
}  


function get_field(val: bv32, which: bv32): bv32 
{  
  val & which  
}  
// 测试方法  

method TestInsertField()  
{  
  var val: bv32 := 0xFFFFFFFF;  
  var which: bv32 := 0x00000F00;  
  var fieldval: bv32 := 0x00000500;  
  
  var result := INSERT_FIELD(val, which, fieldval);  
  
  assert result == 0xFFFFF5FF;  

  // 额外的测试用例  
  assert INSERT_FIELD(0, 0x1, 1) == 0x1;  
  assert INSERT_FIELD(0xFFFFFFFF, 0xF0, 0x50) == 0xFFFFFF5F;  
}  
// method TestInsertField()  
// {  
//   var val: bv32:= 0xFFFFFFFF;  
//   var which: bv32 := 0x0000000000000F00;  
//   var fieldval: bv32 := 0x0000000000000500;  
  
//   var result := INSERT_FIELD(val, which, fieldval);  
  
//   assert result == 0xFFFFF5FF;  
//   assert get_field(result, which) == fieldval;  
//   assert get_field(result, bitnot32(which)) == get_field(val, bitnot32(which));  
// }  
