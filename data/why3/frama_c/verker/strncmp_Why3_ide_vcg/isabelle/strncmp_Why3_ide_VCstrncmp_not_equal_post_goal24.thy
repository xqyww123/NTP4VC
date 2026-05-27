theory strncmp_Why3_ide_VCstrncmp_not_equal_post_goal24
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal24:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes i_5 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_6 :: "int"
  fixes i_7 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a_2; x_2 :: int = offset a; x_3 :: int = offset a_3; x_4 :: int = i_5 + x - x_2; x_5 :: int = l_strnlen t_1 a_1 i_5; x_6 :: int = x + x_5; x_7 :: int = l_strnlen t_1 a_3 i_5; x_8 :: int = i_5 + x; x_10 :: int = x_2 - x; x_11 :: int = t_1 (shift a_3 x_10); x_12 :: int = t_1 (shift a_1 x_10) in \<not>t_1 (shift a_3 i_3) = t_1 (shift a_1 i_3) \<longrightarrow> x + x_1 = x_2 + x_3 \<longrightarrow> x_2 + l_strnlen t_1 a x_4 = x_6 \<longrightarrow> x_1 + l_strnlen t_1 a_2 x_4 = x_3 + x_7 \<longrightarrow> (0 :: int) < i_5 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> x \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> i_3 < x_7 \<longrightarrow> x_2 \<le> x_8 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_6 \<longrightarrow> is_uint8 i_7 \<longrightarrow> is_uint64 i_5 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> p_valid_strn t t_1 a_1 i_5 \<longrightarrow> p_valid_strn t t_1 a_3 i_5 \<longrightarrow> is_uint64 x_4 \<longrightarrow> addr_le a (shift a_1 x_5) \<longrightarrow> addr_le a_2 (shift a_3 x_7) \<longrightarrow> p_valid_strn t t_1 a x_4 \<longrightarrow> p_valid_strn t t_1 a_2 x_4 \<longrightarrow> (if x_8 = x_2 then i_1 = (0 :: int) else to_uint8 (t_1 a) = i_6 \<and> to_uint8 (t_1 a_2) = i_7 \<and> (if i_7 = i_6 then i_1 = (0 :: int) \<and> i_7 = (0 :: int) else i_2 = i \<and> x_8 = i_4 + x_2 \<and> \<not>x_11 = x_12 \<and> x + to_uint64 x_10 = x_2 \<and> x_2 < x + l_strnlen t_1 a_3 (i_4 + x_2 - x) \<and> (if i_7 < i_6 then i_1 = -(1 :: int) else i_1 = (1 :: int)) \<and> (if i_7 < i_6 then i_2 = -(1 :: int) else i_2 = (1 :: int)) \<and> (if to_uint8 x_11 < to_uint8 x_12 then i_2 = -(1 :: int) else i_2 = (1 :: int))) \<and> (i_6 = (0 :: int) \<longrightarrow> x_5 = l_strlen t_1 a_1 \<and> x_6 = x_2 \<and> p_valid_str t t_1 a_1) \<and> (i_7 = (0 :: int) \<longrightarrow> x_7 = l_strlen t_1 a_3 \<and> x + x_7 = x_2 \<and> p_valid_str t t_1 a_3)) \<longrightarrow> (\<forall>(i_8 :: int). (0 :: int) \<le> i_8 \<longrightarrow> i_8 + x < x_2 \<longrightarrow> t_1 (shift a_3 i_8) = t_1 (shift a_1 i_8)) \<longrightarrow> (\<forall>(i_8 :: int). let x_13 :: int = t_1 (shift a_3 i_8); x_14 :: int = t_1 (shift a_1 i_8) in (0 :: int) \<le> i_8 \<longrightarrow> i_8 < x_7 \<longrightarrow> to_uint8 x_13 = to_uint8 x_14 \<longleftrightarrow> x_13 = x_14) \<longrightarrow> (\<exists>(i_8 :: int). let x_13 :: int = t_1 (shift a_3 i_8); x_14 :: int = t_1 (shift a_1 i_8) in \<not>x_13 = x_14 \<and> (0 :: int) \<le> i_8 \<and> i_8 < x_7 \<and> (if to_uint8 x_13 < to_uint8 x_14 then i_1 = -(1 :: int) else i_1 = (1 :: int)) \<and> (\<forall>(i_9 :: int). (0 :: int) \<le> i_9 \<longrightarrow> i_9 < i_8 \<longrightarrow> t_1 (shift a_3 i_9) = t_1 (shift a_1 i_9)))"
  sorry
end
