theory strim_Why3_ide_VCstrim_len_post_5_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype" "frama_c_verker_lib.A_SkipSpaces_A_SkipSpaces"
begin
theorem goal17:
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = l_skip_spaces a; x :: int = base a; x_1 :: int = l_strlen t_2 a; a_3 :: addr = shift a (x_1 - (1 :: int)); x_2 :: int = t_2 a_3; x_3 :: int = t_3 a_1; a_4 :: addr = shift a (-(1 :: int)); a_5 :: addr = shift a_1 (1 :: int); m :: addr \<Rightarrow> int = t_3(a_5 := 0 :: int); x_4 :: int = m a_2; x_5 :: int = l_strlen m a; x_6 :: int = m (shift a_2 (l_strlen m a_2 - (1 :: int))) in base a_2 = x \<longrightarrow> t_2 (shift a x_1) = (0 :: int) \<longrightarrow> \<not>x_2 = (0 :: int) \<longrightarrow> (0 :: int) < x_1 \<longrightarrow> region x \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint8 x_3 \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> addr_le a a_2 \<longrightarrow> is_uint64 x_1 \<longrightarrow> addr_le a_4 a_1 \<longrightarrow> is_sint8 x_4 \<longrightarrow> \<not>p_isspace x_4 \<longrightarrow> p_valid_str t_1 m a \<longrightarrow> p_valid_str t_1 m a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> is_sint8 x_2 \<longrightarrow> addr_le a_2 (shift a x_5) \<longrightarrow> is_sint8 x_6 \<longrightarrow> (if addr_le a a_1 then \<not>p_isspace (t_2 a_1) \<and> (a_4 = a_1 \<or> \<not>p_isspace x_3) else t_3 = t_2 \<and> t_1 = t \<and> (a_4 = a_1 \<or> \<not>p_isspace x_3)) \<longrightarrow> (a_4 = a_1 \<longrightarrow> x_5 = (0 :: int)) \<longrightarrow> (addr_lt a a_1 \<longrightarrow> l_strlen m a_1 = (1 :: int)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x_1 \<longrightarrow> \<not>t_2 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_le a a_6 \<longrightarrow> addr_lt a_6 a_2 \<longrightarrow> p_isspace (m a_6)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_1 a_6 \<longrightarrow> addr_le a_6 a_3 \<longrightarrow> p_isspace (t_2 a_6)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_5 a_6 \<longrightarrow> addr_le a_6 a_3 \<longrightarrow> p_isspace (m a_6)) \<longrightarrow> \<not>p_isspace x_6"
  sorry
end
