theory strlcpy_Why3_ide_VCstrlcpy_size_is_greater_src_post_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal9:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes p :: "bool"
  fixes i :: "int"
  shows "let x :: int = base a_1; x_1 :: int = base a; x_2 :: int = l_strlen t_2 a; a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr \<Rightarrow> int = havoc t_1 t_3 a_2 i_2; a_4 :: addr \<Rightarrow> int = a_3(shift a_1 i_2 := 0 :: int) in \<not>x = x_1 \<longrightarrow> t_2 (shift a x_2) = (0 :: int) \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < l_strlen t_4 a \<longrightarrow> x_2 < i_1 \<longrightarrow> region x_1 \<le> (0 :: int) \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint64 i_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> is_uint64 x_2 \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> (if i_1 = (0 :: int) then t_4 = t_2 else p = False \<and> i_2 = i \<and> t_3 = t_2 \<and> l_strlen t_3 a = i_2 \<and> a_4 = t_4 \<and> l_strlen a_4 a_1 = i_2 \<and> valid_rd t (shift a (0 :: int)) i_2 \<and> valid_rw t a_2 i_2 \<and> p_valid_str t a_4 a_1 \<and> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_2 \<longrightarrow> a_3 (shift a_1 i_4) = a_3 (shift a i_4))) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_2 \<longrightarrow> \<not>t_2 (shift a i_4) = (0 :: int)) \<longrightarrow> t_4 (shift a_1 i_3) = t_4 (shift a i_3)"
  sorry
end
