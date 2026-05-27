theory strcpy_Why3_ide_VCstrcpy_loop_assign_part2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal10:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_2 a_1; x_1 :: int = base a_2; x_2 :: int = base a; x_3 :: int = offset a_2; x_4 :: int = offset a_1; x_5 :: int = l_strlen t_2 a_2; a_4 :: addr = shift a (0 :: int); x_6 :: int = (1 :: int) + x_5 in \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = x_2 \<longrightarrow> x_3 + offset a_3 = offset a + x_4 \<longrightarrow> x_3 + x_5 = x_4 + l_strlen t_2 a_1 \<longrightarrow> havoc t_1 t_3 a_4 x_6 = t_2 \<longrightarrow> (0 :: int) \<le> x_5 \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> addr_le a a_3 \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> p_valid_str t t_3 a_2 \<longrightarrow> addr_le a_1 (shift a_2 x_5) \<longrightarrow> addr_le a_3 (shift a x_5) \<longrightarrow> valid_rw t a_4 ((1 :: int) + l_strlen t_3 a_2) \<longrightarrow> \<not>invalid t a_4 x_6 \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i + x_3 < x_4 \<longrightarrow> t_2 (shift a_2 i) = t_2 (shift a i)) \<longrightarrow> x_5 \<le> l_strlen (t_2(a_3 := x)) a_2"
  sorry
end
