theory strim_Why3_ide_VCstrim_assert_10_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal12:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t_1 :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_2 a; a_3 :: addr = shift a (x - (1 :: int)); x_1 :: int = t_2 a_3; x_2 :: int = t_3 a_2; a_4 :: addr = shift a (-(1 :: int)); a_5 :: addr = shift a_2 (1 :: int); m :: addr \<Rightarrow> int = t_3(a_5 := 0 :: int) in \<not>x = (0 :: int) \<longrightarrow> t_2 (shift a x) = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_2 a \<longrightarrow> is_uint64 x \<longrightarrow> addr_le a_4 a_2 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x_1 \<longrightarrow> (if addr_le a a_2 then a_3 = a_1 \<and> \<not>p_isspace (t_2 a_2) \<and> (a_4 = a_2 \<or> \<not>p_isspace x_2) else t_3 = t_2 \<and> t_1 = t \<and> shift a (l_strlen t_3 a - (1 :: int)) = a_1 \<and> (a_4 = a_2 \<or> \<not>p_isspace x_2)) \<longrightarrow> (a_4 = a_2 \<longrightarrow> l_strlen m a = (0 :: int)) \<longrightarrow> (addr_lt a a_2 \<longrightarrow> l_strlen m a_2 = (1 :: int)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_2 (shift a i) = (0 :: int)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_le a_6 a_1 \<longrightarrow> addr_lt a_5 a_6 \<longrightarrow> p_isspace (m a_6)) \<longrightarrow> (\<forall>(a_6 :: addr). addr_lt a_2 a_6 \<longrightarrow> addr_le a_6 a_3 \<longrightarrow> p_isspace (t_2 a_6)) \<longrightarrow> p_valid_str t_1 m a"
  sorry
end
