theory strncasecmp_Why3_ide_VCstrncasecmp_loop_inv_4_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal6:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = t_1 a; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a_1; x_3 :: int = to_uint8 x_2; x_4 :: int = to_uint64 (i_2 - (1 :: int)); x_5 :: int = offset a; x_6 :: int = offset a_2; x_7 :: int = i_2 + x_5 - x_6; x_8 :: int = l_strnlen t_1 a_2 x_7; x_9 :: int = l_strnlen t_1 a_3 x_7 in \<not>x_1 = (0 :: int) \<longrightarrow> \<not>x_3 = (0 :: int) \<longrightarrow> \<not>x_4 = (0 :: int) \<longrightarrow> \<not>i_2 + x_5 = x_6 \<longrightarrow> offset a_1 + x_6 = x_5 + offset a_3 \<longrightarrow> x_5 + x_8 = x_6 + l_strnlen t_1 a i_2 \<longrightarrow> x_5 + x_9 = x_6 + l_strnlen t_1 a_1 i_2 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> x_6 \<le> x_5 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_3 \<longrightarrow> is_uint8 i_4 \<longrightarrow> is_sint8 i \<longrightarrow> is_sint8 i_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_strn t t_1 a i_2 \<longrightarrow> p_valid_strn t t_1 a_1 i_2 \<longrightarrow> is_uint64 x_7 \<longrightarrow> p_valid_strn t t_1 a_2 x_7 \<longrightarrow> p_valid_strn t t_1 a_3 x_7 \<longrightarrow> addr_le a (shift a_2 x_8) \<longrightarrow> addr_le a_1 (shift a_3 x_9) \<longrightarrow> x_3 = x_1 \<or> i_4 = i_3 \<and> to_uint8 i = i_4 \<and> to_uint8 i_1 = i_4 \<and> l_tolower x = i \<and> l_tolower x_2 = i_1 \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 + x_6 < x_5 \<longrightarrow> l_tolower (t_1 (shift a_3 i_5)) = l_tolower (t_1 (shift a_2 i_5))) \<longrightarrow> (1 :: int) + x_4 = i_2"
  sorry
end
