theory memcmp_Why3_ide_VCmemcmp_complete_not_eq_eq_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal0:
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  shows "let a_6 :: addr = shift a_4 (0 :: int); a_7 :: addr = shift a_5 (0 :: int) in (0 :: int) \<le> i \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_6 i \<longrightarrow> valid_rw t a_7 i \<longrightarrow> separated a_7 i a_6 i \<longrightarrow> (0 :: int) < i \<and> (\<exists>(i_1 :: int). \<not>t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<and> (0 :: int) \<le> i_1 \<and> i_1 < i) \<or> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> t_1 (shift a_3 i_1) = t_1 (shift a_2 i_1))"
  sorry
end
