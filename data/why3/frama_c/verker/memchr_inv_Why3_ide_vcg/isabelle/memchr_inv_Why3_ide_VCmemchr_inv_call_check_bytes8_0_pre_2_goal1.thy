theory memchr_inv_Why3_ide_VCmemchr_inv_call_check_bytes8_0_pre_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a :: "addr"
  shows "let x :: int = to_uint32 (int_of_addr a_1 cmod (8 :: int)) in \<not>x = (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> (17 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint64 i \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t (shift a (0 :: int)) (to_uint32 ((8 :: int) - x))"
  sorry
end
