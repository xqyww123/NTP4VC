theory stpcpy_Why3_ide_VCstpcpy_assert_2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal10:
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_3; x_1 :: int = base a_1; x_2 :: int = offset a_1; x_3 :: int = offset a; x_4 :: int = l_strlen t_2 a_1; a_4 :: addr = shift a_3 (0 :: int); x_5 :: int = (t_2(a_2 := 0 :: int)) (shift a (0 :: int)) in t_2 a = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> x_2 + offset a_2 = x_3 + offset a_3 \<longrightarrow> x_2 + x_4 = x_3 + l_strlen t_2 a \<longrightarrow> havoc t_1 t_3 a_4 ((1 :: int) + x_4) = t_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_3 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> p_valid_str t t_3 a_1 \<longrightarrow> is_sint8 x_5 \<longrightarrow> addr_le a (shift a_1 x_4) \<longrightarrow> addr_le a_2 (shift a_3 x_4) \<longrightarrow> valid_rw t a_4 ((1 :: int) + l_strlen t_3 a_1) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i + x_2 < x_3 \<longrightarrow> t_2 (shift a_3 i) = t_2 (shift a_1 i)) \<longrightarrow> x_5 = (0 :: int)"
  sorry
end
