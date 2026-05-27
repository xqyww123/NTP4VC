theory sysfs_streq_Why3_ide_VCsysfs_streq_assert_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_StrnCmp_A_StrnCmp" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal12:
  fixes a_3 :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes p :: "bool"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  shows "let a_4 :: addr = shift a_3 i; x :: int = t_1 a_4; a_5 :: addr = shift a_2 i; x_1 :: int = t_1 (shift a_2 i_2); x_2 :: int = t_1 (shift a_3 i_2); x_3 :: int = t_1 (shift a_2 i_1); x_4 :: int = t_1 (shift a_3 i_1) in i \<le> l_strlen t_1 a_2 \<longrightarrow> i \<le> l_strlen t_1 a_3 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> p_strnequal t_1 a_3 a_2 i \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a_5 \<longrightarrow> p_valid_str t t_1 a_4 \<longrightarrow> (if x = (0 :: int) then p = False \<and> (0 :: int) \<le> i_1 \<and> i_1 < i \<and> is_uint64 i_1 else p = True \<and> \<not>t_1 a_1 = t_1 a \<and> a_5 = a \<and> a_4 = a_1 \<and> (0 :: int) \<le> i_2 \<and> i_2 < i \<and> is_uint64 i_2) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i \<longrightarrow> t_1 (shift a_3 i_3) = t_1 (shift a_2 i_3)) \<longrightarrow> (if p = True then \<not>x_1 = (0 :: int) \<and> \<not>x_2 = (0 :: int) \<and> x_2 = x_1 else \<not>x_3 = (0 :: int) \<and> \<not>x_4 = (0 :: int) \<and> x_4 = x_3)"
  sorry
end
