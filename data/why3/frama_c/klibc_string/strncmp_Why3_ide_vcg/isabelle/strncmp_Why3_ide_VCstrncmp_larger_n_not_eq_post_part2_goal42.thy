theory strncmp_Why3_ide_VCstrncmp_larger_n_not_eq_post_part2_goal42
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_klibc_string_lib.Compound_Compound"
begin
theorem goal42:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i - i_1; a_2 :: addr = shift a x; a_3 :: addr = shift a_1 x; a_4 :: addr = shift a (0 :: int); a_5 :: addr = shift a_1 (0 :: int) in \<not>i_1 = (0 :: int) \<longrightarrow> \<not>t_1 (shift a_1 i_2) = t_1 (shift a i_2) \<longrightarrow> t_1 a_2 = (0 :: int) \<longrightarrow> t_1 a_3 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rw t a_4 i \<longrightarrow> valid_rw t a_5 i \<longrightarrow> separated a_5 i a_4 i \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 (shift a i) \<longrightarrow> addr_le a_3 (shift a_1 i) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + i_1 < i \<longrightarrow> t_1 (shift a_1 i_3) = t_1 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> \<not>t_1 (shift a i_3) = (0 :: int)) \<longrightarrow> \<not>(\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> \<not>t_1 (shift a_1 i_3) = (0 :: int))"
  sorry
end
