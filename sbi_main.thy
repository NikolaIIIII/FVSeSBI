theory sbi_main
  imports Main
begin
(* Type definitions *)
type_synonym reg_index = nat
type_synonym address = nat
type_synonym size = nat
type_synonym protection = nat
type_synonym mstatus_reg = nat
consts
  MSTATUS_MPP :: nat  (* Assume MPP field starts at bit 11 *)
  MSTATUS_MPIE :: nat  (* Assume MPIE field starts at bit 7 *)
(* Set these constants appropriately based on your target architecture *)
definition MSTATUS_MPP_POS :: nat where "MSTATUS_MPP_POS = 11"  (* Position of MPP field *)
definition MSTATUS_MPIE_POS :: nat where "MSTATUS_MPIE_POS = 7"  (* Position of MPIE field *)

(* Constants for protection flags *)
definition PMP_RWX :: nat where "PMP_RWX = 7"
definition PRV_S :: nat where "PRV_S = 1"

(* Mock functions to simulate hardware interaction *)
definition read_csr :: "mstatus_reg \<Rightarrow> nat" where
"read_csr r = r"

fun write_csr :: "mstatus_reg \<Rightarrow> nat \<Rightarrow> mstatus_reg" where
"write_csr r v = v"

definition update_mstatus :: "mstatus_reg \<Rightarrow> reg_index \<Rightarrow> nat \<Rightarrow> mstatus_reg" where
"update_mstatus m reg val = (m div (2^(reg * 8))) * (2^(reg * 8)) + (val mod (2^8)) * (2^(reg * 8)) + (m mod (2^(reg * 8)))"

definition insert_field :: "mstatus_reg \<Rightarrow> reg_index \<Rightarrow> nat \<Rightarrow> mstatus_reg" where
"insert_field m f v = update_mstatus m f v
"
type_synonym pmp_entry = "address \<times> size \<times> protection"

definition valid_pmp_entry :: "pmp_entry \<Rightarrow> bool" where
"valid_pmp_entry e \<equiv> case e of (addr, sz, prot) \<Rightarrow> addr + sz \<le> 4294967296 \<and> prot \<le> PMP_RWX"


definition sbi_set_pmp :: "reg_index \<Rightarrow> address \<Rightarrow> size \<Rightarrow> protection \<Rightarrow> pmp_entry list \<Rightarrow> pmp_entry list" where
"sbi_set_pmp idx addr sz prot pmps =
  (if idx < length pmps \<and> True  
   then pmps[idx := (addr, sz, prot)]
   else pmps)"

definition mstatus_mpp_set :: "mstatus_reg \<Rightarrow> bool" where
"mstatus_mpp_set m \<equiv> insert_field m MSTATUS_MPP PRV_S = PRV_S"

theorem mstatus_mpp_set_correct:
  assumes "mstatus_mpp_set mstatus"
  shows "read_csr (insert_field mstatus MSTATUS_MPP PRV_S) = PRV_S"
  using assms
  apply (simp add: mstatus_mpp_set_def read_csr_def insert_field_def)
  done

theorem pmp_correctly_configured:
  assumes "pmps \<noteq> []"
  shows "valid_pmp_entry (hd (sbi_set_pmp 1 0x80000000  0x40000  PMP_RWX pmps))"
proof -
  from assms obtain x xs where "pmps = x # xs"
    by (cases pmps) auto
  hence "sbi_set_pmp 1 0x80000000 0x40000 PMP_RWX pmps = ( 0x80000000, 0, PMP_RWX) # xs"
    by (simp add: sbi_set_pmp_def)
  hence "hd (sbi_set_pmp 1 0x80000000 0x40000 PMP_RWX pmps) = ( 0x80000000, 0, PMP_RWX)"
    by simp
  thus ?thesis
    unfolding valid_pmp_entry_def PMP_RWX_def
    by simp
qed

end