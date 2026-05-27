theory strcspn_Why3_ide_VCstrcspn_not_exists_post_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCSpn_A_StrCSpn" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal21:
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_5 :: "addr"
  fixes i :: "int"
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = offset a_4; x_1 :: int = offset a; x_2 :: int = l_strlen t_1 a; x_3 :: int = t_1 a_4; x_4 :: int = t_1 a_5; a_6 :: addr = shift a x_2; x_5 :: int = i + x_1; x_6 :: int = t_1 a_3; a_7 :: addr = shift a_1 (l_strlen t_1 a_1) in x + l_strcspn a_4 a_1 = x_1 + l_strcspn a a_1 \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x \<le> x_1 + x_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_4 \<longrightarrow> is_sint8 x_3 \<longrightarrow> is_sint8 x_4 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_4 \<longrightarrow> is_uint64 (x - x_1) \<longrightarrow> addr_le a_4 a_6 \<longrightarrow> (if x_3 = (0 :: int) then x_5 = x else a_2 = a_1 \<and> a_5 = a_4 \<and> \<not>x_6 = (0 :: int) \<and> x_4 = x_6 \<and> x_5 = offset a_5 \<and> addr_le a_2 a_3 \<and> p_valid_str t t_1 a_3 \<and> p_in_array t_1 a_2 x_4 \<and> p_in_array t_1 a_3 x_4 \<and> addr_le a_3 (shift a_2 (l_strlen t_1 a_2)) \<and> (\<forall>(a_8 :: addr). addr_lt a_8 a_3 \<longrightarrow> addr_le a_2 a_8 \<longrightarrow> \<not>x_4 = t_1 a_8)) \<longrightarrow> (\<forall>(a_9 :: addr) (a_8 :: addr). addr_lt a_9 a_4 \<longrightarrow> addr_le a a_9 \<longrightarrow> addr_le a_1 a_8 \<longrightarrow> addr_lt a_8 a_7 \<longrightarrow> \<not>t_1 a_9 = t_1 a_8) \<longrightarrow> (\<forall>(a_9 :: addr) (a_8 :: addr). addr_le a a_9 \<longrightarrow> addr_le a_1 a_8 \<longrightarrow> addr_lt a_8 a_7 \<longrightarrow> addr_lt a_9 a_6 \<longrightarrow> \<not>t_1 a_9 = t_1 a_8) \<longrightarrow> x_2 = i"
  sorry
end
