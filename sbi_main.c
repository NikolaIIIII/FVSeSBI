#include "asm/csr.h"
//#include "asm/sbi.h"
#include "uart.h"
#include "sbi_trap.h"
#include "printk.h"
#include "sbi_lib.h"

#define FW_JUMP_ADDR 0x80200000

#define BANNER \
"      ___             ___        ___        __  ___\n"\
"    //   ) )        //   ) )   //   ) )      / /\n" \
"   ((         ___  ((         //___/ /      / /\n"\
"      \\    / /___))   \\       / __  (      / /\n"\
"      ) ) / /           ) )  //    ) )    / /\n" \
"((___/ / ( (____ ((___ / / //____/ /   __/ /___\n"


int sbi_set_pmp(int reg_idx, unsigned long start, unsigned long size, unsigned long prot)
{
	int order;
	int pmpcfg_csr, pmpcfg_shift, pmpaddr_csr;
	unsigned long cfgmask, pmpcfg;
	unsigned long addrmask, pmpaddr;

	if (reg_idx > MAX_CSR_PMP)
		return -1;

	order = log2roundup(size);
	if (order < PMP_SHIFT)
		return -1;
	
	printk("%s: start: 0x%lx order %d prot 0x%lx\n", __func__, start, order, prot);
	pmpaddr = start >> PMP_SHIFT;
	pmpcfg_csr   = (CSR_PMPCFG0 + (reg_idx >> 2)) & ~1;
	pmpcfg_shift = (reg_idx & 7) << 3;
	pmpaddr_csr = CSR_PMPADDR0 + reg_idx;
	prot &= ~PMP_A;
	prot |= (order == PMP_SHIFT) ? PMP_A_NA4 : PMP_A_NAPOT;
	cfgmask = ~(0xffUL << pmpcfg_shift);
	pmpcfg	= (read_csr_num(pmpcfg_csr) & cfgmask);
	pmpcfg |= ((prot << pmpcfg_shift) & ~cfgmask);
	if (order > PMP_SHIFT)
	{
		if (order == RISCV_XLEN) {
			pmpaddr = -1UL;
		} else {
			addrmask = (1UL << (order - PMP_SHIFT)) - 1;
			pmpaddr	 &= ~addrmask;
			pmpaddr |= (addrmask >> 1);
		}
	}
	printk("%s: pmpaddr: 0x%lx  pmpcfg 0x%lx, cfs_csr 0x%x addr_csr 0x%x\n",
			__func__, pmpaddr, pmpcfg, pmpcfg_csr, pmpaddr_csr);
	write_csr_num(pmpaddr_csr, pmpaddr);
	write_csr_num(pmpcfg_csr, pmpcfg);

	return 0;
}

static int check_h_extension(void)
{
	return read_csr(misa) & (1 << 7);
}

void sbi_main(void)
{
	unsigned long val;
	uart_init();
	init_printk_done(putchar);
	printk(BANNER);
	sbi_trap_init();
	sbi_set_pmp(0, 0, -1UL, PMP_RWX);
	sbi_set_pmp(1, 0x80000000, 0x40000, PMP_RWX);
	val = read_csr(mstatus);
	val = INSERT_FIELD(val, MSTATUS_MPP, PRV_S);
	val = INSERT_FIELD(val, MSTATUS_MPIE, 0);
	write_csr(mstatus, val);
	delegate_traps();
	write_csr(mepc, FW_JUMP_ADDR);
	write_csr(stvec, FW_JUMP_ADDR);
	write_csr(sie, 0);
	write_csr(satp, 0);
	asm volatile("mret");
}
