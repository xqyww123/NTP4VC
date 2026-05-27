theory strncasecmp_Why3_ide_VCstrncasecmp_not_equal_post_goal23
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal23:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes a_2 :: "addr"
  fixes i_3 :: "int"
  fixes a_3 :: "addr"
  fixes i_5 :: "int"
  fixes i_7 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_8 :: "int"
  fixes i_9 :: "int"
  fixes i_10 :: "int"
  fixes i_11 :: "int"
  fixes i_12 :: "int"
  fixes i_13 :: "int"
  fixes i_14 :: "int"
  fixes i_15 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes i_6 :: "int"
  shows "let x :: int = t_1 a_1; x_1 :: int = offset a; x_2 :: int = offset a_2; x_3 :: int = i_3 + x_1 - x_2; x_4 :: int = l_strnlen t_1 a_2 x_3; x_5 :: int = l_strnlen t_1 a_3 x_3; x_6 :: int = t_1 a; x_7 :: int = to_uint8 x_6; x_8 :: int = to_uint64 (i_5 - (1 :: int)) in \<not>l_tolower (t_1 (shift a_3 i_7)) = l_tolower (t_1 (shift a_2 i_7)) \<longrightarrow> (0 :: int) \<le> i_7 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> i_7 \<le> l_strnlen t_1 a_3 i_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_8 \<longrightarrow> is_uint8 i_9 \<longrightarrow> is_uint8 i_10 \<longrightarrow> is_uint8 i_11 \<longrightarrow> is_uint8 i_12 \<longrightarrow> is_uint8 i_13 \<longrightarrow> is_uint8 i_14 \<longrightarrow> is_uint8 i_15 \<longrightarrow> is_sint8 i \<longrightarrow> is_sint8 i_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> is_uint64 i_3 \<longrightarrow> is_uint64 i_4 \<longrightarrow> is_uint64 i_5 \<longrightarrow> is_uint64 i_6 \<longrightarrow> p_valid_strn t t_1 a_2 i_2 \<longrightarrow> p_valid_strn t t_1 a_3 i_2 \<longrightarrow> \<not>(i_2 = (0 :: int) \<or> i_6 = i_3 \<and> to_uint8 x = i_11 \<and> i_3 + x_1 = i_2 + x_2 \<and> offset a_1 + x_2 = x_1 + offset a_3 \<and> x_1 + x_4 = x_2 + l_strnlen t_1 a i_3 \<and> x_1 + x_5 = x_2 + l_strnlen t_1 a_1 i_3 \<and> (0 :: int) \<le> i_3 \<and> x_2 \<le> x_1 \<and> addr_le a_2 a \<and> addr_le a_3 a_1 \<and> p_valid_strn t t_1 a i_3 \<and> p_valid_strn t t_1 a_1 i_3 \<and> addr_le a (shift a_2 x_4) \<and> addr_le a_1 (shift a_3 x_5) \<and> (if i_11 = (0 :: int) then i_10 = (0 :: int) \<and> i_15 = (0 :: int) \<and> x_7 = i_10 else x_7 = i_8 \<and> (if i_8 = (0 :: int) then i_10 = (0 :: int) \<and> i_11 = (0 :: int) \<and> i_14 = (0 :: int) \<and> i_14 = i_11 \<and> i_15 = (0 :: int) \<and> i_15 = i_11 \<and> i_15 = i_14 else i_9 = i_8 \<and> i_12 = i_11 \<and> i_15 = i_10 \<and> (if i_11 = i_8 then i_5 = i_3 \<and> i_10 = i_8 \<and> i_15 = i_11 \<and> x_8 = (0 :: int) else i_4 = i_3 \<and> i_15 = i_13 \<and> to_uint8 i = i_10 \<and> to_uint8 i_1 = i_15 \<and> l_tolower (to_sint8 x_6) = i \<and> l_tolower (to_sint8 x) = i_1 \<and> (\<not>i_15 = i_10 \<or> i_5 = i_4 \<and> x_8 = (0 :: int))))) \<and> (\<forall>(i_16 :: int). (0 :: int) \<le> i_16 \<longrightarrow> i_16 + x_2 < x_1 \<longrightarrow> l_tolower (t_1 (shift a_3 i_16)) = l_tolower (t_1 (shift a_2 i_16))))"
  sorry
end
