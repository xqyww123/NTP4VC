theory strspn_Why3_ide_VCstrspn_loop_inv_7_established_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal13:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_1; x_1 :: int = offset a_1; x_2 :: int = offset a; x_3 :: int = l_strlen t_1 a; a_3 :: addr = shift a_2 (l_strlen t_1 a_2) in \<not>x = (0 :: int) \<longrightarrow> x_1 + l_strspn a_1 a_2 = x_2 + l_strspn a a_2 \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_2 + x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> is_uint64 (x_1 - x_2) \<longrightarrow> addr_le a_1 (shift a x_3) \<longrightarrow> (\<forall>(a_4 :: addr). addr_lt a_4 a_1 \<longrightarrow> addr_le a a_4 \<longrightarrow> (\<exists>(a_5 :: addr). t_1 a_4 = t_1 a_5 \<and> addr_le a_2 a_5 \<and> addr_lt a_5 a_3)) \<longrightarrow> addr_le a_2 a_2 \<and> addr_le a_2 a_3"
  sorry
end
