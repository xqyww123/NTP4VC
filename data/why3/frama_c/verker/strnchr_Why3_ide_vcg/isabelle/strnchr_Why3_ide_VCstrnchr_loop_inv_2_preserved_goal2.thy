theory strnchr_Why3_ide_VCstrnchr_loop_inv_2_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = to_sint8 i_1; x_2 :: int = offset a_1; x_3 :: int = offset a; x_4 :: int = i + x_3 - x_2; x_5 :: int = l_strnlen t_1 a_1 x_4; a_2 :: addr = shift a_1 x_5; a_3 :: addr = shift a (1 :: int) in \<not>i = (0 :: int) \<longrightarrow> \<not>x = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> x_2 + x_5 = x_3 + l_strnlen t_1 a i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_2 \<le> x_3 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> is_uint64 x_4 \<longrightarrow> p_valid_strn t t_1 a_1 x_4 \<longrightarrow> addr_le a a_2 \<longrightarrow> (\<forall>(a_4 :: addr). addr_lt a_4 a \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> \<not>t_1 a_4 = x_1) \<longrightarrow> addr_le a_1 a_3 \<and> addr_le a_3 a_2"
  sorry
end
