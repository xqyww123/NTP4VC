theory strreplace_Why3_ide_VCstrreplace_loop_inv_5_preserved_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal9:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let x :: int = l_strlen t_2 a_1; a_3 :: addr = shift a_1 x; a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 (shift a_1 (0 :: int)) x; a_5 :: int = a_4 a; x_1 :: int = t_2 a_2 in t_2 a_3 = (0 :: int) \<longrightarrow> \<not>a_5 = (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint8 i \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> is_uint64 x \<longrightarrow> addr_lt a_2 (shift a (1 :: int)) \<longrightarrow> addr_le a a_3 \<longrightarrow> is_sint8 a_5 \<longrightarrow> p_valid_str t a_4 a \<longrightarrow> p_valid_str t a_4 a_1 \<longrightarrow> (if a_5 = x_1 then a_4(a := i) = t_3 else a_4 = t_3) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> \<not>t_2 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_le a a_6 \<longrightarrow> addr_lt a_6 a_3 \<longrightarrow> a_4 a_6 = t_2 a_6) \<longrightarrow> (\<forall>(a_6 :: addr). x_1 = t_2 a_6 \<longrightarrow> addr_lt a_6 a \<longrightarrow> addr_le a_1 a_6 \<longrightarrow> a_4 a_6 = i) \<longrightarrow> (\<forall>(a_6 :: addr). let x_2 :: int = t_2 a_6 in \<not>x_1 = x_2 \<longrightarrow> addr_lt a_6 a \<longrightarrow> addr_le a_1 a_6 \<longrightarrow> a_4 a_6 = x_2) \<longrightarrow> t_3 a_2 = i"
  sorry
end
