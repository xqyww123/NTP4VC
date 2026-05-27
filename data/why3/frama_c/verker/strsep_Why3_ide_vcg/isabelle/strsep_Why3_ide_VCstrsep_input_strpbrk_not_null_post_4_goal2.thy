theory strsep_Why3_ide_VCstrsep_input_strpbrk_not_null_post_4_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_StrPBrk_A_StrPBrk" "frama_c_verker_lib.A_StrSpn_A_StrSpn"
begin
theorem goal2:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_4 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_5 :: addr = t_2 a; a_6 :: addr = l_strpbrk a_5 a_1; a_7 :: addr = shift a_1 (l_strlen t_1 a_1); a_8 :: addr = shift a_5 (l_strlen t_1 a_5) in \<not>a_5 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_3 = t_1 a_2 \<longrightarrow> \<not>a_6 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> t_1 a_6 = t_1 a_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> addr_le a_5 a_3 \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_5 \<longrightarrow> addr_le a_5 a_6 \<longrightarrow> addr_lt a_2 a_7 \<longrightarrow> addr_le a_4 a_7 \<longrightarrow> addr_lt a_3 a_8 \<longrightarrow> addr_lt a_6 a_8 \<longrightarrow> (\<forall>(a_10 :: addr) (a_9 :: addr). addr_le a_1 a_9 \<longrightarrow> addr_le a_5 a_10 \<longrightarrow> addr_lt a_10 a_6 \<longrightarrow> addr_lt a_9 a_7 \<longrightarrow> \<not>t_1 a_10 = t_1 a_9) \<longrightarrow> p_valid_str t (t_1(a_6 := 0 :: int)) a_5"
  sorry
end
