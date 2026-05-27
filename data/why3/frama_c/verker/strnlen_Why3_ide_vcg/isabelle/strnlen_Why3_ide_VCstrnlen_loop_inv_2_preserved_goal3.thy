theory strnlen_Why3_ide_VCstrnlen_loop_inv_2_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal3:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = offset a_1; x_2 :: int = offset a; x_3 :: int = i + x_2 - x_1; x_4 :: int = l_strnlen t_1 a_1 x_3; a_2 :: addr = shift a_1 x_4; a_3 :: addr = shift a (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> x_1 + x_4 = x_2 + l_strnlen t_1 a i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_1 \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> is_uint64 x_3 \<longrightarrow> p_valid_strn t t_1 a_1 x_3 \<longrightarrow> addr_le a a_2 \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_1 < x_2 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> addr_le a_1 a_3 \<and> addr_le a_3 a_2"
  sorry
end
