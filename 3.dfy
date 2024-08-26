// 定义 UART 寄存器地址  
const UART_IER: bv32 := 0x1;  
const UART_LCR: bv32 := 0x3;  
const UART_DLL: bv32 := 0x0;  
const UART_DLM: bv32 := 0x1;  
const UART_FCR: bv32 := 0x2;  

// 定义 UART 默认波特率  
const UART_DEFAULT_BAUD: bv32 := 115200;  

class UARTState {  
  var registers: map<bv32, bv8>;  

  constructor()  
    ensures registers == map[]  
  {  
    registers := map[];  
  }  
method writeb(value: bv8, reg: bv32)  
    modifies this`registers  
    ensures registers == old(registers)[reg := value]  
    // 分别验证以下三个条件  
    ensures reg in registers && registers[reg] == value  
    ensures forall r :: r in registers && r != reg ==>   
      registers[r] == if r in old(registers) then old(registers)[r] else 0  
    ensures forall r :: r in old(registers) ==> r in registers  
  {  
    registers := registers[reg := value];  

    // 验证第一个条件  
    // assert reg in registers && registers[reg] == value; 
    assert reg in registers;  
    assert registers[reg] == value;  
    // 验证第二个条件  
    assert forall r :: r in registers && r != reg ==>   
      registers[r] == if r in old(registers) then old(registers)[r] else 0;  

    // 验证第三个条件  
    assert forall r :: r in old(registers) ==> r in registers;  
  }  
  predicate HasRegisterValue(reg: bv32, value: bv8)  
    reads this  
  {  
    reg in registers && registers[reg] == value  
  }  

}

// method uart_init(uart: UARTState, uart16550_clock: bv32)  
//   modifies uart`registers  
//   requires uart16550_clock > 0  
//   ensures uart.HasRegisterValue(UART_IER, 0x1)  
//   ensures uart.HasRegisterValue(UART_LCR, 0x3)  
//   ensures uart.HasRegisterValue(UART_FCR, 0xc7)  
//   ensures UART_DLL in uart.registers && UART_DLM in uart.registers  
// {  
//   var divisor := uart16550_clock / (16 * UART_DEFAULT_BAUD);  

//   uart.writeb(0, UART_IER);  
//   uart.writeb(0x80, UART_LCR);  
//   uart.writeb((divisor & 0xFF) as bv8, UART_DLL);  
//   uart.writeb(((divisor >> 8) & 0xFF) as bv8, UART_DLM);  
//   uart.writeb(0x3, UART_LCR);  
//   uart.writeb(0xc7, UART_FCR);  
//   uart.writeb(0x1, UART_IER);  

// //   辅助断言  
//   assert uart.HasRegisterValue(UART_IER, 0x1);  
//   assert uart.HasRegisterValue(UART_LCR, 0x3);  
//   assert uart.HasRegisterValue(UART_FCR, 0xc7);  
//   assert UART_DLL in uart.registers && UART_DLM in uart.registers;  
// }
method uart_init(uart: UARTState, uart16550_clock: bv32)  
  modifies uart`registers  
  requires uart16550_clock > 0  
  ensures uart.HasRegisterValue(UART_IER, 0x1)  
  ensures uart.HasRegisterValue(UART_LCR, 0x3)  
  ensures uart.HasRegisterValue(UART_FCR, 0xc7)  
  ensures UART_DLL in uart.registers && UART_DLM in uart.registers  
{  
  var divisor := uart16550_clock / (16 * UART_DEFAULT_BAUD);  

  uart.writeb(0, UART_IER);  
  assert uart.registers[UART_IER] == 0;  

  uart.writeb(0x80, UART_LCR);  
  assert uart.registers[UART_LCR] == 0x80;  

  uart.writeb((divisor & 0xFF) as bv8, UART_DLL);  
  assert UART_DLL in uart.registers;  

  uart.writeb(((divisor >> 8) & 0xFF) as bv8, UART_DLM);  
  assert UART_DLM in uart.registers;  

  uart.writeb(0x3, UART_LCR);  
  assert uart.registers[UART_LCR] == 0x3;  

  uart.writeb(0xc7, UART_FCR);  
  assert uart.registers[UART_FCR] == 0xc7;  

  uart.writeb(0x1, UART_IER);  
  assert uart.registers[UART_IER] == 0x1;  

  assert uart.HasRegisterValue(UART_IER, 0x1);  
  assert uart.HasRegisterValue(UART_LCR, 0x3);  
  assert uart.HasRegisterValue(UART_FCR, 0xc7);  
  assert UART_DLL in uart.registers && UART_DLM in uart.registers;  
}
// UART 初始化函数  
// method uart_init(uart: UARTState, uart16550_clock: bv32)  
//   modifies uart  
//   requires uart16550_clock > 0  
//   ensures UART_IER in uart.registers && uart.registers[UART_IER] == 0x1  
//   ensures UART_LCR in uart.registers && uart.registers[UART_LCR] == 0x3  
//   ensures UART_FCR in uart.registers && uart.registers[UART_FCR] == 0xc7  
//   ensures UART_DLL in uart.registers && UART_DLM in uart.registers  
// {  
//   var divisor := uart16550_clock / (16 * UART_DEFAULT_BAUD);  

//   // 禁用中断  
//   uart.writeb(0, UART_IER);  
//   assert UART_IER in uart.registers && uart.registers[UART_IER] == 0;  

//   // 启用 DLAB 并设置波特率除数  
//   uart.writeb(0x80, UART_LCR);  
//   assert UART_LCR in uart.registers && uart.registers[UART_LCR] == 0x80;  

//   uart.writeb((divisor & 0xFF) as bv8, UART_DLL);  
//   assert UART_DLL in uart.registers;  

//   uart.writeb(((divisor >> 8) & 0xFF) as bv8, UART_DLM);  
//   assert UART_DLM in uart.registers;  

//   // 设置 8 位数据，无奇偶校验，1 位停止位  
//   uart.writeb(0x3, UART_LCR);  
//   assert UART_LCR in uart.registers && uart.registers[UART_LCR] == 0x3;  

//   // 启用 FIFO，清空 FIFO，设置 14 字节阈值  
//   uart.writeb(0xc7, UART_FCR);  
//   assert UART_FCR in uart.registers && uart.registers[UART_FCR] == 0xc7;  

//   // 启用接收缓冲区满中断  
//   uart.writeb(0x1, UART_IER);  
//   assert UART_IER in uart.registers && uart.registers[UART_IER] == 0x1;  

//   // 最终验证所有后置条件  
//   assert UART_IER in uart.registers && uart.registers[UART_IER] == 0x1;  
//   assert UART_LCR in uart.registers && uart.registers[UART_LCR] == 0x3;  
//   assert UART_FCR in uart.registers && uart.registers[UART_FCR] == 0xc7;  
//   assert UART_DLL in uart.registers && UART_DLM in uart.registers;  
// }
// 测试方法  

method TestUARTInit()  
{  
  var uart := new UARTState();  
  var clock: bv32 := 1843200; // 假设时钟频率为 1.8432 MHz  
  
  uart_init(uart, clock);  

  assert UART_IER in uart.registers && uart.registers[UART_IER] == 0x1;  
  assert UART_LCR in uart.registers && uart.registers[UART_LCR] == 0x3;  
  assert UART_FCR in uart.registers && uart.registers[UART_FCR] == 0xc7;  

  assert UART_DLL in uart.registers;  
  assert UART_DLM in uart.registers;  
}