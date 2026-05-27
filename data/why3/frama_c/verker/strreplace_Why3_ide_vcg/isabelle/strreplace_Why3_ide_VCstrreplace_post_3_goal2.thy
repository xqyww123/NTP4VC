theory strreplace_Why3_ide_VCstrreplace_post_3_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = l_strlen t_2 a_1; a_3 :: addr = shift a_1 x; a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 (shift a_1 (0 :: int)) x; x_1 :: int = t_2 a_2 in offset a_1 + x = offset a \<longrightarrow> t_2 a_3 = (0 :: int) \<longrightarrow> a_4 a = (0 :: int) \<longrightarrow> l_strlen a_4 a = (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint8 i \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> is_uint64 x \<longrightarrow> addr_lt a_2 a_3 \<longrightarrow> addr_le a a_3 \<longrightarrow> p_valid_str t a_4 a \<longrightarrow> p_valid_str t a_4 a_1 \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> \<not>t_2 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> (\<forall>(a_5 :: addr). addr_le a a_5 \<longrightarrow> addr_lt a_5 a_3 \<longrightarrow> a_4 a_5 = t_2 a_5) \<longrightarrow> (\<forall>(a_5 :: addr). x_1 = t_2 a_5 \<longrightarrow> addr_lt a_5 a \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> a_4 a_5 = i) \<longrightarrow> (\<forall>(a_5 :: addr). let x_2 :: int = t_2 a_5 in \<not>x_1 = x_2 \<longrightarrow> addr_lt a_5 a \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> a_4 a_5 = x_2) \<longrightarrow> a_4 a_2 = i"
  sorry
end
