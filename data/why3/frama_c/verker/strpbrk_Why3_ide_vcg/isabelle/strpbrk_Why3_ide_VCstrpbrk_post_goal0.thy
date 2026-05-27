theory strpbrk_Why3_ide_VCstrpbrk_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrPBrk_A_StrPBrk" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_3 :: "addr"
  shows "let a_6 :: addr = l_strpbrk a_5 a_4; x :: int = t_1 a_2; x_1 :: int = t_2 a_1; x_2 :: int = t_2 a; a_7 :: addr = shift a_4 (l_strlen t_2 a_4) in a_6 = l_strpbrk a_2 a_4 \<longrightarrow> region (base a_4) \<le> (0 :: int) \<longrightarrow> region (base a_5) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_5 a_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_4 \<longrightarrow> p_valid_str t t_1 a_5 \<longrightarrow> addr_le a_2 (shift a_5 (l_strlen t_1 a_5)) \<longrightarrow> (if x = (0 :: int) then Mk_addr (0 :: int) (0 :: int) = a else a_2 = a \<and> a_3 = a \<and> a_3 = a_2 \<and> t_2 = t_1 \<and> \<not>x_1 = (0 :: int) \<and> x_1 = x_2 \<and> addr_le a_4 a_1 \<and> addr_le a_5 a \<and> p_valid_str t t_2 a_1 \<and> addr_lt a (shift a_5 (l_strlen t_2 a_5)) \<and> addr_lt a_1 a_7 \<and> addr_le a_1 a_7 \<and> (p_in_array t_2 a_4 x_2 \<longrightarrow> p_in_array t_2 a_1 x_2) \<and> (\<forall>(a_8 :: addr). addr_lt a_8 a_1 \<longrightarrow> addr_le a_4 a_8 \<longrightarrow> \<not>x_2 = t_2 a_8) \<and> (\<forall>(a_9 :: addr) (a_8 :: addr). addr_lt a_9 a \<longrightarrow> addr_le a_4 a_8 \<longrightarrow> addr_le a_5 a_9 \<longrightarrow> addr_lt a_8 a_7 \<longrightarrow> \<not>t_2 a_9 = t_2 a_8)) \<longrightarrow> (\<forall>(a_9 :: addr) (a_8 :: addr). addr_lt a_9 a_2 \<longrightarrow> addr_le a_4 a_8 \<longrightarrow> addr_le a_5 a_9 \<longrightarrow> addr_lt a_8 (shift a_4 (l_strlen t_1 a_4)) \<longrightarrow> \<not>t_1 a_9 = t_1 a_8) \<longrightarrow> a_6 = a"
  sorry
end
