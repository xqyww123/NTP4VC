theory strlcpy_Why3_ide_VCstrlcpy_size_is_lower_src_assign_normal_part6_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal15:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = l_strlen t_2 a; a_2 :: addr = shift a_1 (0 :: int); x_3 :: int = to_uint64 (i - (1 :: int)); a_3 :: addr = shift a_1 x_3; a_4 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 x_3 in \<not>x = x_1 \<longrightarrow> t_2 (shift a x_2) = (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> i \<le> x_2 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> is_uint64 x_2 \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rd t (shift a (0 :: int)) x_3 \<longrightarrow> valid_rw t a_2 x_3 \<longrightarrow> \<not>invalid t a_3 (1 :: int) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_2 \<longrightarrow> \<not>t_2 (shift a i_1) = (0 :: int)) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_3 \<longrightarrow> a_4 (shift a_1 i_1) = a_4 (shift a i_1)) \<longrightarrow> included a_3 (1 :: int) a_2 i"
  sorry
end
