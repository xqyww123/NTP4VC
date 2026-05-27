theory strnchr_Why3_ide_VCstrnchr_loop_inv_6_preserved_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal7:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = t_1 a; x_1 :: int = to_sint8 i_1; x_2 :: int = offset a_1; x_3 :: int = i + x_2; x_4 :: int = offset a; x_5 :: int = i + x_2 - x_4; x_6 :: int = l_strnlen t_1 a_1 i in \<not>x = (0 :: int) \<longrightarrow> \<not>x = x_1 \<longrightarrow> \<not>x_3 = x_4 \<longrightarrow> x_4 + l_strnlen t_1 a x_5 = x_2 + x_6 \<longrightarrow> x_2 \<le> x_4 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_4 \<le> x_3 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_strn t t_1 a_1 i \<longrightarrow> addr_lt a_2 (shift a (1 :: int)) \<longrightarrow> is_uint64 x_5 \<longrightarrow> addr_le a (shift a_1 x_6) \<longrightarrow> p_valid_strn t t_1 a x_5 \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> \<not>t_1 a_3 = x_1) \<longrightarrow> \<not>t_1 a_2 = x_1"
  sorry
end
