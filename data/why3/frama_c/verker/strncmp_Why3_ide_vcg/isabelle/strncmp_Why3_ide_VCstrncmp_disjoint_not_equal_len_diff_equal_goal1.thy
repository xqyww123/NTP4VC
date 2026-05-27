theory strncmp_Why3_ide_VCstrncmp_disjoint_not_equal_len_diff_equal_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strnlen t_1 a_1 i; x_1 :: int = l_strnlen t_1 a i in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> p_valid_strn t t_1 a_1 i \<longrightarrow> (i \<le> (0 :: int) \<or> \<not>i = (0 :: int) \<and> (\<not>x = x_1 \<or> i \<le> (0 :: int) \<or> (\<exists>(i_1 :: int). \<not>t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<and> (0 :: int) \<le> i_1 \<and> i_1 < x)) \<or> (\<forall>(i_1 :: int). t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<or> i_1 < (0 :: int) \<or> x \<le> i_1)) \<and> (x = x_1 \<or> i \<le> (0 :: int) \<or> \<not>i = (0 :: int) \<and> (\<not>x = x_1 \<or> i \<le> (0 :: int) \<or> (\<exists>(i_1 :: int). \<not>t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<and> (0 :: int) \<le> i_1 \<and> i_1 < x)) \<or> (\<exists>(i_1 :: int). \<not>t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<and> (0 :: int) \<le> i_1 \<and> i_1 < x))"
  sorry
end
