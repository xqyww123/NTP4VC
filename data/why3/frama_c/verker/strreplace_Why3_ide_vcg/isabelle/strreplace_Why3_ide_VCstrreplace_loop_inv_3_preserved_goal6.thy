theory strreplace_Why3_ide_VCstrreplace_loop_inv_3_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = l_strlen t_2 a_1; a_2 :: addr = shift a_1 x; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 (shift a_1 (0 :: int)) x; a_4 :: int = a_3 a; a_5 :: addr = shift a (1 :: int) in t_2 a_2 = (0 :: int) \<longrightarrow> \<not>a_4 = (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint8 i \<longrightarrow> is_sint8 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> is_uint64 x \<longrightarrow> addr_le a a_2 \<longrightarrow> is_sint8 a_4 \<longrightarrow> p_valid_str t a_3 a \<longrightarrow> p_valid_str t a_3 a_1 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> \<not>t_2 (shift a_1 i_2) = (0 :: int)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_le a a_6 \<longrightarrow> addr_lt a_6 a_2 \<longrightarrow> a_3 a_6 = t_2 a_6) \<longrightarrow> (\<forall>(a_6 :: addr). t_2 a_6 = i \<longrightarrow> addr_lt a_6 a \<longrightarrow> addr_le a_1 a_6 \<longrightarrow> a_3 a_6 = i_1) \<longrightarrow> (\<forall>(a_6 :: addr). let x_1 :: int = t_2 a_6 in \<not>x_1 = i \<longrightarrow> addr_lt a_6 a \<longrightarrow> addr_le a_1 a_6 \<longrightarrow> a_3 a_6 = x_1) \<longrightarrow> addr_le a_1 a_5 \<and> addr_le a_5 a_2"
  sorry
end
