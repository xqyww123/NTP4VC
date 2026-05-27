theory strcspn_Why3_ide_VCstrcspn_loop_inv_9_preserved_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCSpn_A_StrCSpn" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal15:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_1; x_1 :: int = t_1 a_3; x_2 :: int = offset a_3; x_3 :: int = offset a_2; x_4 :: int = l_strlen t_1 a_2; a_4 :: addr = shift a (l_strlen t_1 a) in \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> \<not>x_1 = x \<longrightarrow> x_2 + l_strcspn a_3 a = x_3 + l_strcspn a_2 a \<longrightarrow> x_3 \<le> x_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_2 \<le> x_3 + x_4 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_uint64 (x_2 - x_3) \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> addr_le a_3 (shift a_2 x_4) \<longrightarrow> (p_in_array t_1 a x_1 \<longrightarrow> p_in_array t_1 a_1 x_1) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_5 a_1 \<longrightarrow> addr_le a a_5 \<longrightarrow> \<not>x_1 = t_1 a_5) \<longrightarrow> (\<forall>(a_6 :: addr) (a_5 :: addr). addr_lt a_6 a_3 \<longrightarrow> addr_le a a_5 \<longrightarrow> addr_le a_2 a_6 \<longrightarrow> addr_lt a_5 a_4 \<longrightarrow> \<not>t_1 a_6 = t_1 a_5) \<longrightarrow> p_valid_str t t_1 (shift a_1 (1 :: int))"
  sorry
end
