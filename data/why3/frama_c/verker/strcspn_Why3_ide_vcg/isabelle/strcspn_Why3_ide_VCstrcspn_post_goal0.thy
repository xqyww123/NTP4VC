theory strcspn_Why3_ide_VCstrcspn_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCSpn_A_StrCSpn" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_3; x_1 :: int = offset a_2; x_2 :: int = l_strcspn a_2 a; x_3 :: int = l_strlen t_1 a_2; x_4 :: int = t_1 a_3; x_5 :: int = t_2 a_4; x_6 :: int = i + x_1; x_7 :: int = t_2 a_1 in x + l_strcspn a_3 a = x_1 + x_2 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x \<le> x_1 + x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x_4 \<longrightarrow> is_sint8 x_5 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_uint64 (x - x_1) \<longrightarrow> addr_le a_3 (shift a_2 x_3) \<longrightarrow> (if x_4 = (0 :: int) then x_6 = x else a_4 = a_3 \<and> t_2 = t_1 \<and> \<not>x_7 = (0 :: int) \<and> x_5 = x_7 \<and> x_6 = offset a_4 \<and> addr_le a a_1 \<and> p_valid_str t t_2 a_1 \<and> p_in_array t_2 a x_5 \<and> p_in_array t_2 a_1 x_5 \<and> addr_le a_1 (shift a (l_strlen t_2 a)) \<and> (\<forall>(a_5 :: addr). addr_lt a_5 a_1 \<longrightarrow> addr_le a a_5 \<longrightarrow> \<not>x_5 = t_2 a_5)) \<longrightarrow> (\<forall>(a_6 :: addr) (a_5 :: addr). addr_lt a_6 a_3 \<longrightarrow> addr_le a a_5 \<longrightarrow> addr_le a_2 a_6 \<longrightarrow> addr_lt a_5 (shift a (l_strlen t_1 a)) \<longrightarrow> \<not>t_1 a_6 = t_1 a_5) \<longrightarrow> x_2 = i"
  sorry
end
