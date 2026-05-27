theory strncat_Why3_ide_VCstrncat_assert_3_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal16:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes p :: "bool"
  shows "let x :: int = l_strlen t_2 a; a_3 :: addr = shift a x; x_1 :: int = l_strnlen t_2 a_1 i_2; a_4 :: addr = shift a_1 x_1; x_2 :: int = t_2 a_4; a_5 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 ((1 :: int) + x_1); a_6 :: int = a_5 a_1; a_7 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 ((1 :: int) + l_strnlen t_2 a_1 i_3); a_8 :: addr = shift a i_1; a_9 :: addr = shift a i in \<not>i_2 = (0 :: int) \<longrightarrow> t_2 a_3 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 + x \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i_2 \<longrightarrow> is_uint64 i_3 \<longrightarrow> addr_le a_1 a_1 \<longrightarrow> is_sint8 (t_3 a_2) \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> is_uint64 x \<longrightarrow> p_valid_strn t t_2 a_1 i_2 \<longrightarrow> is_sint8 (t_3 (shift a_2 (-(1 :: int)))) \<longrightarrow> is_uint64 x_1 \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_3 a_3 \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_2 a_3 \<longrightarrow> valid_rw t (shift a (0 :: int)) ((1 :: int) + i_2 + x) \<longrightarrow> addr_le a_3 (shift a (x + x_1)) \<longrightarrow> is_sint8 a_6 \<longrightarrow> p_valid_str t a_5 a_1 \<longrightarrow> (if a_6 = (0 :: int) then p = False \<and> a_5(a_3 := 0 :: int) = t_3 \<and> (0 :: int) \<le> i \<and> i < x else p = True \<and> i_3 = i_2 \<and> to_uint64 (i_3 - (1 :: int)) = (0 :: int) \<and> shift a ((1 :: int) + x) = a_2 \<and> a_7(a_2 := 0 :: int, a_3 := a_7 a_1) = t_3 \<and> (0 :: int) \<le> i_1 \<and> i_1 < x) \<longrightarrow> ((\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 \<le> i_2 \<longrightarrow> \<not>t_2 (shift a_1 i_4) = (0 :: int)) \<longrightarrow> x_1 = i_2) \<longrightarrow> ((\<exists>(i_4 :: int). t_2 (shift a_1 i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 \<le> i_2) \<longrightarrow> x_2 = (0 :: int)) \<longrightarrow> ((\<exists>(i_4 :: int). t_2 (shift a_1 i_4) = (0 :: int) \<and> (0 :: int) \<le> i_4 \<and> i_4 \<le> i_2) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_1 \<longrightarrow> \<not>t_2 (shift a_1 i_4) = (0 :: int))) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x \<longrightarrow> \<not>t_2 (shift a i_4) = (0 :: int)) \<longrightarrow> (if p = True then t_3 a_8 = t_2 a_8 else t_3 a_9 = t_2 a_9)"
  sorry
end
