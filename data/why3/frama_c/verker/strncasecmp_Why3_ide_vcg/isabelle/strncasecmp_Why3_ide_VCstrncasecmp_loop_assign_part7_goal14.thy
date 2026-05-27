theory strncasecmp_Why3_ide_VCstrncasecmp_loop_assign_part7_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal14:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i :: "int"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a_1; x_3 :: int = to_uint8 x_2; x_4 :: int = l_tolower x_2; x_5 :: int = l_tolower x; x_6 :: int = offset a; x_7 :: int = offset a_2; x_8 :: int = i + x_6 - x_7; x_9 :: int = l_strnlen t_1 a_2 x_8; x_10 :: int = l_strnlen t_1 a_3 x_8 in \<not>x_1 = (0 :: int) \<longrightarrow> \<not>x_3 = (0 :: int) \<longrightarrow> \<not>x_3 = x_1 \<longrightarrow> to_uint8 x_4 = to_uint8 x_5 \<longrightarrow> \<not>to_uint64 (i - (1 :: int)) = (0 :: int) \<longrightarrow> \<not>i + x_6 = x_7 \<longrightarrow> offset a_1 + x_7 = x_6 + offset a_3 \<longrightarrow> x_6 + x_9 = x_7 + l_strnlen t_1 a i \<longrightarrow> x_6 + x_10 = x_7 + l_strnlen t_1 a_1 i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_7 \<le> x_6 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x_5 \<longrightarrow> is_sint8 x_4 \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> p_valid_strn t t_1 a_1 i \<longrightarrow> is_uint64 x_8 \<longrightarrow> p_valid_strn t t_1 a_2 x_8 \<longrightarrow> p_valid_strn t t_1 a_3 x_8 \<longrightarrow> addr_le a (shift a_2 x_9) \<longrightarrow> addr_le a_1 (shift a_3 x_10) \<longrightarrow> \<not>(\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_7 < x_6 \<longrightarrow> l_tolower (t_1 (shift a_3 i_1)) = l_tolower (t_1 (shift a_2 i_1)))"
  sorry
end
