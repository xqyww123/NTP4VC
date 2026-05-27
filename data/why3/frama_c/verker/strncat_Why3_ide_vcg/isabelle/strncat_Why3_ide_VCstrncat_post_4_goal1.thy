theory strncat_Why3_ide_VCstrncat_post_4_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal1:
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes p :: "bool"
  fixes p_1 :: "bool"
  fixes p_2 :: "bool"
  fixes p_3 :: "bool"
  fixes p_4 :: "bool"
  fixes t_1 :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = l_strlen t_4 a_3; x_1 :: int = t_5 a_2; a_4 :: addr = shift a_3 (0 :: int); x_2 :: int = i + i_2; x_3 :: int = to_uint64 x_2; a_5 :: addr = shift a i; x_4 :: int = t_3 a; m :: addr \<Rightarrow> int = t_3(a_1 := 0 :: int); m_1 :: addr \<Rightarrow> int = t_3(a_2 := 0 :: int, a_1 := x_4) in x \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> i_1 < x + l_strnlen t_5 a i_4 \<longrightarrow> i_4 + x \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_4 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_2 \<longrightarrow> is_uint64 i_3 \<longrightarrow> is_uint64 i_4 \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_4 a_3 \<longrightarrow> p_valid_strn t t_4 a i_4 \<longrightarrow> is_sint8 (t_5 (shift a_2 (-(1 :: int)))) \<longrightarrow> valid_rw t a_4 ((1 :: int) + i_4 + x) \<longrightarrow> (if i_4 = (0 :: int) then t_5 = t_4 else p = False \<and> p_1 = False \<and> p_2 = False \<and> p_3 = False \<and> p_4 = False \<and> t_1 = t \<and> t_4 a_1 = (0 :: int) \<and> shift a_3 i_2 = a_1 \<and> x = i_2 \<and> l_strnlen t_4 a i_4 = i \<and> shift a_3 ((1 :: int) + i_2) = a_2 \<and> havoc t_2 t_4 a_1 ((1 :: int) + i) = t_3 \<and> t_5 (shift a_3 x_3) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> addr_le a a \<and> addr_le a_1 a_1 \<and> addr_le a_3 a_1 \<and> p_valid_str t_1 t_3 a \<and> p_valid_str t_1 t_4 a_1 \<and> p_valid_str t_1 t_4 a_3 \<and> p_valid_str t_1 t_5 a_3 \<and> p_valid_strn t_1 t_4 a i_4 \<and> addr_le a a_5 \<and> addr_le a_1 (shift a_3 x_2) \<and> valid_rw t_1 a_4 ((1 :: int) + x_3) \<and> (if x_4 = (0 :: int) then i_4 = i_3 \<and> m = t_5 \<and> (\<forall>(i_5 :: int). let a_6 :: addr = shift a_3 i_5 in (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_2 \<longrightarrow> m a_6 = t_4 a_6) else i_3 = (0 :: int) \<and> m_1 = t_5 \<and> to_uint64 (i_4 - (1 :: int)) = (0 :: int) \<and> (\<forall>(i_5 :: int). let a_6 :: addr = shift a_3 i_5 in (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_2 \<longrightarrow> m_1 a_6 = t_4 a_6)) \<and> (i_3 = (0 :: int) \<longrightarrow> i_4 = i \<and> x_1 = (0 :: int)) \<and> ((0 :: int) < i_3 \<longrightarrow> i = (0 :: int) \<and> t_5 a_1 = (0 :: int) \<and> t_5 (shift a (0 :: int)) = (0 :: int)) \<and> ((\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 \<le> i_4 \<longrightarrow> \<not>t_4 (shift a i_5) = (0 :: int)) \<longrightarrow> i_4 = i) \<and> ((\<exists>(i_5 :: int). t_4 (shift a i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 \<le> i_4) \<longrightarrow> t_4 a_5 = (0 :: int)) \<and> ((\<exists>(i_5 :: int). t_4 (shift a i_5) = (0 :: int) \<and> (0 :: int) \<le> i_5 \<and> i_5 \<le> i_4) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i \<longrightarrow> \<not>t_4 (shift a i_5) = (0 :: int))) \<and> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_2 \<longrightarrow> \<not>t_4 (shift a_3 i_5) = (0 :: int))) \<longrightarrow> t_5 (shift a (i_1 - x)) = t_5 (shift a_3 i_1)"
  sorry
end
