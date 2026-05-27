theory strncasecmp_Why3_ide_VCstrncasecmp_assign_normal_part11_goal20
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal20:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a_1; x_3 :: int = to_uint8 x_2; x_4 :: int = offset a_2; x_5 :: int = offset a; x_6 :: int = i + x_4 - x_5; x_7 :: int = l_strnlen t_1 a_2 i; x_8 :: int = l_strnlen t_1 a_3 i in \<not>i = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> \<not>x_3 = (0 :: int) \<longrightarrow> \<not>x_3 = x_1 \<longrightarrow> offset a_1 + x_4 = x_5 + offset a_3 \<longrightarrow> x_4 + l_strnlen t_1 a x_6 = x_5 + x_7 \<longrightarrow> x_4 + l_strnlen t_1 a_1 x_6 = x_5 + x_8 \<longrightarrow> x_4 \<le> x_5 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x_5 \<le> i + x_4 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 (l_tolower x) \<longrightarrow> is_sint8 (l_tolower x_2) \<longrightarrow> p_valid_strn t t_1 a_2 i \<longrightarrow> p_valid_strn t t_1 a_3 i \<longrightarrow> is_uint64 x_6 \<longrightarrow> addr_le a (shift a_2 x_7) \<longrightarrow> addr_le a_1 (shift a_3 x_8) \<longrightarrow> p_valid_strn t t_1 a x_6 \<longrightarrow> p_valid_strn t t_1 a_1 x_6 \<longrightarrow> \<not>(\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_4 < x_5 \<longrightarrow> l_tolower (t_1 (shift a_3 i_1)) = l_tolower (t_1 (shift a_2 i_1)))"
  sorry
end
