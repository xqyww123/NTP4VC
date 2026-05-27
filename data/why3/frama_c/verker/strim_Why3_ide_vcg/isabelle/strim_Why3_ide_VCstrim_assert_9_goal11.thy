theory strim_Why3_ide_VCstrim_assert_9_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a; a_3 :: addr = shift a (x - (1 :: int)); x_1 :: int = t_1 a_3; x_2 :: int = t_3 a_1; a_4 :: addr = shift a_1 (1 :: int); a_5 :: addr = shift a (-(1 :: int)); m :: addr \<Rightarrow> int = t_3(a_4 := 0 :: int) in \<not>x = (0 :: int) \<longrightarrow> t_1 (shift a x) = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> is_uint64 x \<longrightarrow> addr_lt a_4 a_2 \<longrightarrow> addr_le a_5 a_1 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x_1 \<longrightarrow> (if addr_le a a_1 then t_2 = t_1 \<and> \<not>p_isspace (t_2 a_1) \<and> (a_5 = a_1 \<or> \<not>p_isspace x_2) else t_3 = t_1 \<and> (a_5 = a_1 \<or> \<not>p_isspace x_2)) \<longrightarrow> (a_5 = a_1 \<longrightarrow> l_strlen m a = (0 :: int)) \<longrightarrow> (addr_lt a a_1 \<longrightarrow> l_strlen m a_1 = (1 :: int)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_1 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_1 a_6 \<longrightarrow> addr_le a_6 a_3 \<longrightarrow> p_isspace (t_1 a_6)) \<longrightarrow> p_isspace (m a_2)"
  sorry
end
