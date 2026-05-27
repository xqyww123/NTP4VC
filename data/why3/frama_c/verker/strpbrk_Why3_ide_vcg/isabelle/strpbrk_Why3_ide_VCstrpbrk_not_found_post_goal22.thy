theory strpbrk_Why3_ide_VCstrpbrk_not_found_post_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrPBrk_A_StrPBrk" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal22:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = t_1 a_1; a_4 :: addr = shift a_3 (l_strlen t_1 a_3); a_5 :: addr = shift a_2 (l_strlen t_1 a_2) in \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> x_1 = x \<longrightarrow> l_strpbrk a_3 a_2 = l_strpbrk a a_2 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_2 a_1 \<longrightarrow> addr_le a_3 a \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_lt a a_4 \<longrightarrow> addr_lt a_1 a_5 \<longrightarrow> addr_le a a_4 \<longrightarrow> addr_le a_1 a_5 \<longrightarrow> (p_in_array t_1 a_2 x \<longrightarrow> p_in_array t_1 a_1 x) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_6 a_1 \<longrightarrow> addr_le a_2 a_6 \<longrightarrow> \<not>x = t_1 a_6) \<longrightarrow> (\<forall>(a_7 :: addr) (a_6 :: addr). addr_lt a_7 a \<longrightarrow> addr_le a_2 a_6 \<longrightarrow> addr_le a_3 a_7 \<longrightarrow> addr_lt a_6 a_5 \<longrightarrow> \<not>t_1 a_7 = t_1 a_6) \<longrightarrow> (\<forall>(a_7 :: addr) (a_6 :: addr). addr_le a_2 a_6 \<longrightarrow> addr_le a_3 a_7 \<longrightarrow> addr_lt a_6 a_5 \<longrightarrow> addr_lt a_7 a_4 \<longrightarrow> \<not>t_1 a_7 = t_1 a_6) \<longrightarrow> Mk_addr (0 :: int) (0 :: int) = a"
  sorry
end
