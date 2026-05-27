theory strncasecmp_Why3_ide_VCstrncasecmp_equal_post_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal22:
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes i_8 :: "int"
  fixes i_5 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_6 :: "int"
  fixes i_7 :: "int"
  fixes i_9 :: "int"
  fixes i_10 :: "int"
  fixes i_11 :: "int"
  fixes i_12 :: "int"
  fixes i_13 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = offset a_2; x_1 :: int = offset a; x_3 :: int = i_3 + x - x_1; x_4 :: int = l_strnlen t_1 a_2 i_3; x_5 :: int = l_strnlen t_1 a_3 i_3; x_6 :: int = i_3 + x; x_7 :: int = t_1 a; x_8 :: int = t_1 a_1; x_9 :: int = to_uint8 x_8; x_10 :: int = to_uint8 x_7; x_11 :: int = i_2 + i_8; x_12 :: int = i_5 + x_1; x_13 :: int = to_uint64 (i_3 + x - (1 :: int) - x_1) in \<not>i_3 = (0 :: int) \<longrightarrow> offset a_1 + x = x_1 + offset a_3 \<longrightarrow> x + l_strnlen t_1 a x_3 = x_1 + x_4 \<longrightarrow> x + l_strnlen t_1 a_1 x_3 = x_1 + x_5 \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x_1 \<le> x_6 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_6 \<longrightarrow> is_uint8 i_7 \<longrightarrow> is_uint8 i_8 \<longrightarrow> is_uint8 i_9 \<longrightarrow> is_uint8 i_10 \<longrightarrow> is_uint8 i_11 \<longrightarrow> is_uint8 i_12 \<longrightarrow> is_uint8 i_13 \<longrightarrow> is_sint8 i \<longrightarrow> is_sint8 i_1 \<longrightarrow> is_sint32 i_2 \<longrightarrow> is_uint64 i_3 \<longrightarrow> is_uint64 i_4 \<longrightarrow> is_uint64 i_5 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x_7 \<longrightarrow> is_sint8 x_8 \<longrightarrow> p_valid_strn t t_1 a_2 i_3 \<longrightarrow> p_valid_strn t t_1 a_3 i_3 \<longrightarrow> is_uint64 x_3 \<longrightarrow> addr_le a (shift a_2 x_4) \<longrightarrow> addr_le a_1 (shift a_3 x_5) \<longrightarrow> p_valid_strn t t_1 a x_3 \<longrightarrow> p_valid_strn t t_1 a_1 x_3 \<longrightarrow> (if x_9 = (0 :: int) then i_13 = (0 :: int) \<and> x_10 = i_8 \<and> x_11 = (0 :: int) else x_10 = i_6 \<and> (if i_6 = (0 :: int) then i_8 = (0 :: int) \<and> i_12 = i_2 \<and> i_13 = i_2 \<and> i_13 = i_12 \<and> x_9 = i_2 else i_7 = i_6 \<and> x_9 = i_9 \<and> x_11 = i_13 \<and> (if i_9 = i_6 then i_8 = i_6 \<and> i_13 = i_9 \<and> x_12 = x_6 \<and> x_13 = (0 :: int) else i_10 = i_9 \<and> i_13 = i_11 \<and> to_uint8 i = i_8 \<and> to_uint8 i_1 = i_13 \<and> l_tolower x_7 = i \<and> l_tolower x_8 = i_1 \<and> i_4 + x_1 = x_6 \<and> (\<not>i_13 = i_8 \<or> x_12 = x_6 \<and> x_13 = (0 :: int))))) \<longrightarrow> (\<forall>(i_14 :: int). (0 :: int) \<le> i_14 \<longrightarrow> i_14 + x < x_1 \<longrightarrow> l_tolower (t_1 (shift a_3 i_14)) = l_tolower (t_1 (shift a_2 i_14))) \<longrightarrow> (\<forall>(i_14 :: int). (0 :: int) \<le> i_14 \<longrightarrow> i_14 \<le> x_5 \<longrightarrow> l_tolower (t_1 (shift a_3 i_14)) = l_tolower (t_1 (shift a_2 i_14))) \<longrightarrow> i_2 = (0 :: int)"
  sorry
end
