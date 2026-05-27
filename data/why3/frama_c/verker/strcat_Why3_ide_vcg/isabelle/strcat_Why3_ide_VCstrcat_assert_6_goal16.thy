theory strcat_Why3_ide_VCstrcat_assert_6_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal16:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_2 a; a_2 :: addr = shift a x; m :: addr \<Rightarrow> int = t_3(a_2 := 0 :: int); x_1 :: int = l_strlen t_3 a_1; x_2 :: int = l_strlen t_2 a_1 in t_3 a_1 = (0 :: int) \<longrightarrow> t_2 a_2 = (0 :: int) \<longrightarrow> m (shift a_1 (0 :: int)) = (0 :: int) \<longrightarrow> havoc t_1 t_2 a_2 ((1 :: int) + x_1) = t_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x + x_2 \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> addr_le a_1 a_1 \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> p_valid_str t t_3 a_1 \<longrightarrow> is_uint64 x \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 (shift a_1 x_1) \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> p_valid_str t t_2 a_2 \<longrightarrow> valid_rw t (shift a (0 :: int)) ((1 :: int) + x + x_2) \<longrightarrow> addr_le a_2 (shift a (x + x_1)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_2 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_3 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(i :: int). let a_3 :: addr = shift a i in (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> m a_3 = t_2 a_3) \<longrightarrow> l_strlen m a_1 = (0 :: int)"
  sorry
end
