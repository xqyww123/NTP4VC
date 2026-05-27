theory strncasecmp_Why3_ide_VCstrncasecmp_loop_inv_5_preserved_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.A_Ctype_A_Ctype"
begin
theorem goal7:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes i_2 :: "int"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes i_5 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_1 :: "int \<Rightarrow> int"
  shows "let x :: int = t_2 a; x_1 :: int = to_uint8 x; x_2 :: int = t_2 a_1; x_3 :: int = to_uint8 x_2; x_4 :: int = offset a_2; x_5 :: int = offset a; x_7 :: int = to_uint64 (i_2 + x_4 - (1 :: int) - x_5); x_8 :: int = i_2 + x_4 - x_5; x_9 :: int = l_strnlen t_2 a_2 i_2; x_10 :: int = l_strnlen t_2 a_3 i_2; x_11 :: int = i_2 + x_4 in \<not>i_2 = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> \<not>x_3 = (0 :: int) \<longrightarrow> offset a_1 + x_4 = x_5 + offset a_3 \<longrightarrow> \<not>x_7 = (0 :: int) \<longrightarrow> x_4 + l_strnlen t_2 a x_8 = x_5 + x_9 \<longrightarrow> x_4 + l_strnlen t_2 a_1 x_8 = x_5 + x_10 \<longrightarrow> x_4 \<le> x_5 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> x_5 \<le> x_11 \<longrightarrow> linked t \<longrightarrow> sconst t_2 \<longrightarrow> is_uint8 i_4 \<longrightarrow> is_uint8 i_5 \<longrightarrow> is_sint8 i \<longrightarrow> is_sint8 i_1 \<longrightarrow> is_uint64 i_2 \<longrightarrow> is_uint64 i_3 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_strn t t_2 a_2 i_2 \<longrightarrow> p_valid_strn t t_2 a_3 i_2 \<longrightarrow> is_uint64 x_8 \<longrightarrow> addr_le a (shift a_2 x_9) \<longrightarrow> addr_le a_1 (shift a_3 x_10) \<longrightarrow> p_valid_strn t t_2 a x_8 \<longrightarrow> p_valid_strn t t_2 a_1 x_8 \<longrightarrow> (if x_3 = x_1 then t_3 = t_2 \<and> t_1 = t else i_5 = i_4 \<and> to_uint8 i = i_5 \<and> to_uint8 i_1 = i_5 \<and> l_tolower x = i \<and> l_tolower x_2 = i_1 \<and> i_3 + x_5 = x_11) \<longrightarrow> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 + x_4 < x_5 \<longrightarrow> l_tolower (t_2 (shift a_3 i_6)) = l_tolower (t_2 (shift a_2 i_6))) \<longrightarrow> p_valid_strn t_1 t_3 (shift a (1 :: int)) x_7 \<and> p_valid_strn t_1 t_3 (shift a_1 (1 :: int)) x_7"
  sorry
end
