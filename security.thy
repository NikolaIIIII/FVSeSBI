theory security
imports Main
begin

type_synonym reg = int
type_synonym state = "reg \<Rightarrow> int"

consts
  sp :: reg        (* Stack Pointer Register *)
  t0 :: reg        (* Temporary Register 0 *)
  mscratch :: reg  (* Machine Scratch Register *)
  mie :: reg       (* Machine Interrupt Enable Register *)
  zero :: reg      (* Constant Zero Register, assumed to be correctly initialized to 0 *)
consts
  stacks_start :: int
definition csrw :: "reg \<Rightarrow> reg \<Rightarrow> state \<Rightarrow> state" where
"csrw csr r s \<equiv> s(csr := s r)"

definition add :: "reg \<Rightarrow> reg \<Rightarrow> reg \<Rightarrow> state \<Rightarrow> state" where
"add rd rs1 rs2 s \<equiv> s(rd := s rs1 + s rs2)"

definition li :: "reg \<Rightarrow> int  \<Rightarrow> state \<Rightarrow> state" where
"li rd im s \<equiv> s(rd := im)"

definition init_t0 :: "state \<Rightarrow> state" where
"init_t0 s \<equiv> li t0 4096 s"

definition init_sequence :: "state \<Rightarrow> state" where
"init_sequence s \<equiv>
  let s = s(mie := s zero) in     
  let s = s(sp := stacks_start + s t0) in
  let s = s(mscratch := s sp) in 
  s"
theorem correct_initialization:
  assumes "s t0 = 4096"
    and "0 < stacks_start"  (* Ensure stacks_start is positive *)
    and "s zero = 0"  (* Typically, zero register always holds 0 *)
  shows "init_sequence s mscratch \<noteq> 0"
  using assms
  unfolding init_sequence_def
  apply simp
  done
end