theory strlcat_Why3_ide_VCstrlcat_assign_normal_part8_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal8:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_2 a; x_1 :: int = l_strlen t_2 a_1; a_2 :: addr = shift a_1 x_1; x_2 :: int = to_uint64 (i_1 - x_1); a_3 :: addr = shift a_1 (i + x_1); a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 i in t_2 (shift a x) = (0 :: int) \<longrightarrow> t_2 a_2 = (0 :: int) \<longrightarrow> x_1 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i < x_2 \<longrightarrow> x + x_1 \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> p_valid_str t t_2 a_1 \<longrightarrow> is_uint64 x \<longrightarrow> is_uint64 x_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) ((1 :: int) + i_1) \<longrightarrow> valid_rw t a_2 i \<longrightarrow> p_valid_str t t_2 a_2 \<longrightarrow> \<not>invalid t a_3 (1 :: int) \<longrightarrow> (if x_2 \<le> x then to_uint64 (x_2 - (1 :: int)) = i else x = i) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x \<longrightarrow> \<not>t_2 (shift a i_2) = (0 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x_1 \<longrightarrow> \<not>t_2 (shift a_1 i_2) = (0 :: int)) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> a_4 (shift a_1 (i_2 + x_1)) = a_4 (shift a i_2)) \<longrightarrow> included a_3 (1 :: int) a_2 ((1 :: int) + x)"
  sorry
end
