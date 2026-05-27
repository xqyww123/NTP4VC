theory strpbrk_Why3_ide_VCstrpbrk_found_post_2_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrPBrk_A_StrPBrk" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal20:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_8 :: "addr"
  fixes a_7 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_6 :: "addr"
  shows "let x :: int = t_1 a_2; a_9 :: addr = shift a_4 (l_strlen t_1 a_4); a_10 :: addr = shift a_5 (l_strlen t_1 a_5); x_1 :: int = t_1 a_1; x_2 :: int = t_1 a in t_1 a_8 = t_1 a_7 \<longrightarrow> l_strpbrk a_5 a_4 = l_strpbrk a_2 a_4 \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_4 a_7 \<longrightarrow> addr_le a_5 a_2 \<longrightarrow> addr_le a_5 a_8 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_4 \<longrightarrow> p_valid_str t t_1 a_5 \<longrightarrow> addr_lt a_7 a_9 \<longrightarrow> addr_lt a_8 a_10 \<longrightarrow> addr_le a_2 a_10 \<longrightarrow> (if x = (0 :: int) then Mk_addr (0 :: int) (0 :: int) = a else a_2 = a \<and> a_3 = a \<and> a_3 = a_2 \<and> a_6 = a_5 \<and> \<not>x_1 = (0 :: int) \<and> x_1 = x_2 \<and> addr_le a_4 a_1 \<and> addr_le a_6 a \<and> p_valid_str t t_1 a_1 \<and> addr_lt a (shift a_6 (l_strlen t_1 a_6)) \<and> addr_lt a_1 a_9 \<and> addr_le a_1 a_9 \<and> (p_in_array t_1 a_4 x_2 \<longrightarrow> p_in_array t_1 a_1 x_2) \<and> (\<forall>(a_11 :: addr). addr_lt a_11 a_1 \<longrightarrow> addr_le a_4 a_11 \<longrightarrow> \<not>x_2 = t_1 a_11) \<and> (\<forall>(a_12 :: addr) (a_11 :: addr). addr_lt a_12 a \<longrightarrow> addr_le a_4 a_11 \<longrightarrow> addr_le a_6 a_12 \<longrightarrow> addr_lt a_11 a_9 \<longrightarrow> \<not>t_1 a_12 = t_1 a_11)) \<longrightarrow> (\<forall>(a_12 :: addr) (a_11 :: addr). addr_lt a_12 a_2 \<longrightarrow> addr_le a_4 a_11 \<longrightarrow> addr_le a_5 a_12 \<longrightarrow> addr_lt a_11 a_9 \<longrightarrow> \<not>t_1 a_12 = t_1 a_11) \<longrightarrow> (\<exists>(a_11 :: addr). x_2 = t_1 a_11 \<and> addr_le a_4 a_11 \<and> addr_le a_11 a_9)"
  sorry
end
