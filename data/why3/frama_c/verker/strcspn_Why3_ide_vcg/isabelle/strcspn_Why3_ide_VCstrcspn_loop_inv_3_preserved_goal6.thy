theory strcspn_Why3_ide_VCstrcspn_loop_inv_3_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCSpn_A_StrCSpn" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_3; x_1 :: int = offset a_3; x_2 :: int = offset a; x_3 :: int = l_strlen t_1 a; a_4 :: addr = shift a_1 (l_strlen t_1 a_1) in t_1 a_2 = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> x_1 + l_strcspn a_3 a_1 = x_2 + l_strcspn a a_1 \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_2 + x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> \<not>p_in_array t_1 a_1 x \<longrightarrow> is_uint64 (x_1 - x_2) \<longrightarrow> addr_le a_2 a_4 \<longrightarrow> addr_le a_3 (shift a x_3) \<longrightarrow> (\<forall>(a_5 :: addr). addr_lt a_5 a_2 \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> \<not>x = t_1 a_5) \<longrightarrow> (\<forall>(a_6 :: addr) (a_5 :: addr). addr_lt a_6 a_3 \<longrightarrow> addr_le a a_6 \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> addr_lt a_5 a_4 \<longrightarrow> \<not>t_1 a_6 = t_1 a_5) \<longrightarrow> x_2 + to_uint64 ((1 :: int) + x_1 - x_2) = (1 :: int) + x_1"
  sorry
end
