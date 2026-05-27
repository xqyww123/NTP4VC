theory memchr_inv_Why3_ide_VCmemchr_inv_call_check_bytes8_0_pre_3_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal2:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_2 :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  shows "let x :: int = t_2 a in \<not>i = (0 :: int) \<longrightarrow> \<not>x = i_1 \<longrightarrow> to_uint32 (int_of_addr a_2 cmod (8 :: int)) = (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> (17 :: int) \<le> i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> is_uint64 x \<longrightarrow> valid_rw t (shift a_2 (0 :: int)) i_2 \<longrightarrow> valid_rd t_1 (shift a_1 (0 :: int)) (8 :: int)"
  sorry
end
