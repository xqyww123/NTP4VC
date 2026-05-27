theory strchrnul_Why3_ide_VCstrchrnul_exists_post_2_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strchrnul_A_Strchrnul" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = t_1 (shift a_1 i); x_1 :: int = l_strlen t_1 a_1; x_2 :: int = t_1 a in x = to_sint8 i_1 \<longrightarrow> l_strchrnul t_1 a_1 x = l_strchrnul t_1 a x \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i_1 \<longrightarrow> addr_lt a_2 a \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a (shift a_1 x_1) \<longrightarrow> (x_2 = (0 :: int) \<longrightarrow> offset a_1 + x_1 = offset a) \<longrightarrow> x_2 = (0 :: int) \<or> x = x_2 \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> \<not>x = t_1 a_3) \<longrightarrow> \<not>x = t_1 a_2"
  sorry
end
