theory strpbrk_Why3_ide_VCstrpbrk_found_post_goal19
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrPBrk_A_StrPBrk" "frama_c_verker_lib.A_StrSpn_A_StrSpn" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal19:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_5 :: addr = shift a_1 (l_strlen t_1 a_1); a_6 :: addr = shift a_2 (l_strlen t_1 a_2) in t_1 a = (0 :: int) \<longrightarrow> t_1 a_4 = t_1 a_3 \<longrightarrow> l_strpbrk a_2 a_1 = l_strpbrk a a_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_2 a_4 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> addr_lt a_3 a_5 \<longrightarrow> addr_lt a_4 a_6 \<longrightarrow> addr_le a a_6 \<longrightarrow> (\<forall>(a_8 :: addr) (a_7 :: addr). addr_lt a_8 a \<longrightarrow> addr_le a_1 a_7 \<longrightarrow> addr_le a_2 a_8 \<longrightarrow> addr_lt a_7 a_5 \<longrightarrow> \<not>t_1 a_8 = t_1 a_7) \<longrightarrow> addr_le a_2 (Mk_addr (0 :: int) (0 :: int)) \<and> addr_lt (Mk_addr (0 :: int) (0 :: int)) a_6"
  sorry
end
