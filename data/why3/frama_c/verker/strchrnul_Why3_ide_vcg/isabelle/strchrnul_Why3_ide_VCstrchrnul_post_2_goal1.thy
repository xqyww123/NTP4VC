theory strchrnul_Why3_ide_VCstrchrnul_post_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strchrnul_A_Strchrnul" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal1:
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = to_sint8 i; a_2 :: addr = l_strchrnul t_1 a_1 x; x_1 :: int = t_1 a; x_2 :: int = l_strlen t_1 a_1 in a_2 = l_strchrnul t_1 a x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> addr_le a (shift a_1 x_2) \<longrightarrow> (x_1 = (0 :: int) \<longrightarrow> offset a_1 + x_2 = offset a) \<longrightarrow> x_1 = (0 :: int) \<or> x_1 = x \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> \<not>t_1 a_3 = x) \<longrightarrow> a_2 = a"
  sorry
end
