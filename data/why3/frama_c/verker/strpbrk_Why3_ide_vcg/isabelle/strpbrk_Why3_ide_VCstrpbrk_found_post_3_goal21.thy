theory strpbrk_Why3_ide_VCstrpbrk_found_post_3_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrPBrk_A_StrPBrk" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal21:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes a_7 :: "addr"
  fixes a_6 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_9 :: "addr"
  fixes a_8 :: "addr"
  fixes a_5 :: "addr"
  shows "let x :: int = t_1 a_1; a_10 :: addr = shift a_3 (l_strlen t_1 a_3); a_11 :: addr = shift a_4 (l_strlen t_1 a_4); x_1 :: int = t_1 a; x_2 :: int = t_1 a_2 in t_1 a_7 = t_1 a_6 \<longrightarrow> l_strpbrk a_4 a_3 = l_strpbrk a_1 a_3 \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_lt a_9 a_2 \<longrightarrow> addr_le a_3 a_6 \<longrightarrow> addr_le a_3 a_8 \<longrightarrow> addr_le a_4 a_1 \<longrightarrow> addr_le a_4 a_7 \<longrightarrow> addr_le a_4 a_9 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> p_valid_str t t_1 a_4 \<longrightarrow> addr_lt a_6 a_10 \<longrightarrow> addr_lt a_7 a_11 \<longrightarrow> addr_lt a_8 a_10 \<longrightarrow> addr_le a_1 a_11 \<longrightarrow> (if x = (0 :: int) then Mk_addr (0 :: int) (0 :: int) = a_2 else a_2 = a_1 \<and> a_5 = a_4 \<and> \<not>x_1 = (0 :: int) \<and> x_2 = x_1 \<and> addr_le a_3 a \<and> addr_le a_5 a_2 \<and> p_valid_str t t_1 a \<and> addr_lt a a_10 \<and> addr_lt a_2 (shift a_5 (l_strlen t_1 a_5)) \<and> addr_le a a_10 \<and> (p_in_array t_1 a_3 x_2 \<longrightarrow> p_in_array t_1 a x_2) \<and> (\<forall>(a_12 :: addr). addr_lt a_12 a \<longrightarrow> addr_le a_3 a_12 \<longrightarrow> \<not>x_2 = t_1 a_12) \<and> (\<forall>(a_13 :: addr) (a_12 :: addr). addr_lt a_13 a_2 \<longrightarrow> addr_le a_3 a_12 \<longrightarrow> addr_le a_5 a_13 \<longrightarrow> addr_lt a_12 a_10 \<longrightarrow> \<not>t_1 a_13 = t_1 a_12)) \<longrightarrow> (\<forall>(a_13 :: addr) (a_12 :: addr). addr_lt a_13 a_1 \<longrightarrow> addr_le a_3 a_12 \<longrightarrow> addr_le a_4 a_13 \<longrightarrow> addr_lt a_12 a_10 \<longrightarrow> \<not>t_1 a_13 = t_1 a_12) \<longrightarrow> \<not>t_1 a_9 = t_1 a_8"
  sorry
end
