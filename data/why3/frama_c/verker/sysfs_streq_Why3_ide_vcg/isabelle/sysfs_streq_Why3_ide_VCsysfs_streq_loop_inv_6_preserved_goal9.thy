theory sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_6_preserved_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_StrnCmp_A_StrnCmp" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal9:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i; x :: int = t_1 a_2; a_3 :: addr = shift a i; x_1 :: int = t_1 a_3 in \<not>x = (0 :: int) \<longrightarrow> x = x_1 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> l_strlen t_1 a \<longrightarrow> i \<le> l_strlen t_1 a_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_1 < to_uint64 ((1 :: int) + i) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_strnequal t_1 a_1 a i \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> t_1 (shift a_1 i_2) = t_1 (shift a i_2)) \<longrightarrow> t_1 (shift a_1 i_1) = t_1 (shift a i_1)"
  sorry
end
