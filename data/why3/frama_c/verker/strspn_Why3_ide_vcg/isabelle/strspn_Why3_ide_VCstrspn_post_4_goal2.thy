theory strspn_Why3_ide_VCstrspn_post_4_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_4 :: "addr"
  shows "let x :: int = offset a_1; x_1 :: int = offset a; x_2 :: int = l_strspn a a_3; x_3 :: int = l_strlen t_1 a; x_4 :: int = t_1 a_1; x_5 :: int = t_2 a_2; x_6 :: int = i + x_1 in x + l_strspn a_1 a_3 = x_1 + x_2 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x \<le> x_1 + x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_1 \<longrightarrow> is_sint8 x_4 \<longrightarrow> is_sint8 x_5 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_uint64 (x - x_1) \<longrightarrow> addr_le a_1 (shift a x_3) \<longrightarrow> (if x_4 = (0 :: int) then x_6 = x else a_2 = a_1 \<and> t_2 = t_1 \<and> t_2 a_4 = (0 :: int) \<and> x_6 = offset a_2 \<and> addr_le a_3 a_4 \<and> p_valid_str t t_2 a_4 \<and> \<not>p_in_array t_2 a_3 x_5 \<and> addr_le a_4 (shift a_3 (l_strlen t_2 a_3)) \<and> (\<forall>(a_5 :: addr). addr_lt a_5 a_4 \<longrightarrow> addr_le a_3 a_5 \<longrightarrow> \<not>x_5 = t_2 a_5)) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_5 a_1 \<longrightarrow> addr_le a a_5 \<longrightarrow> (\<exists>(a_6 :: addr). t_1 a_5 = t_1 a_6 \<and> addr_le a_3 a_6 \<and> addr_lt a_6 (shift a_3 (l_strlen t_1 a_3)))) \<longrightarrow> x_2 = i"
  sorry
end
