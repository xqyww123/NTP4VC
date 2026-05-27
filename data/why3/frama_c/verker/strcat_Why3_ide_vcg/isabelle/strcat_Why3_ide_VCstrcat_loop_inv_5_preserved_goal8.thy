theory strcat_Why3_ide_VCstrcat_loop_inv_5_preserved_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal8:
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_3 a_1; x_1 :: int = l_strlen t_2 a; a_2 :: addr = shift a x_1; x_2 :: int = l_strlen t_3 a_1; x_3 :: int = l_strlen t_2 a_1; a_3 :: addr = shift a ((1 :: int) + x_1) in \<not>x = (0 :: int) \<longrightarrow> t_2 a_2 = (0 :: int) \<longrightarrow> havoc t_1 t_2 a_2 ((1 :: int) + x_2) = t_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_1 + x_3 \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> addr_le a_1 a_1 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> p_valid_str t t_3 a_1 \<longrightarrow> is_uint64 x_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 (shift a_1 x_2) \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> p_valid_str t t_2 a_2 \<longrightarrow> valid_rw t (shift a (0 :: int)) ((1 :: int) + x_1 + x_3) \<longrightarrow> addr_le a_2 (shift a (x_1 + x_2)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> \<not>t_2 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> \<not>t_3 (shift a i) = (0 :: int)) \<longrightarrow> addr_le a_2 a_3 \<and> addr_le a_3 (shift a (x_1 + l_strlen (t_3(a_2 := x)) a_1))"
  sorry
end
