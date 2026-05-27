theory memcmp_Why3_ide_VCmemcmp_not_eq_post_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal10:
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  shows "let a_6 :: addr = shift a_4 (0 :: int); a_7 :: addr = shift a_5 (0 :: int) in \<not>t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<longrightarrow> (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_6 i \<longrightarrow> valid_rw t a_7 i \<longrightarrow> separated a_7 i a_6 i \<longrightarrow> \<not>(\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> t_1 (shift a_3 i_2) = t_1 (shift a_2 i_2))"
  sorry
end
