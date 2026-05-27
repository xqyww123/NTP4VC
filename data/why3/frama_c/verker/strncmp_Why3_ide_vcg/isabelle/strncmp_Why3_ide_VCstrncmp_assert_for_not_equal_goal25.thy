theory strncmp_Why3_ide_VCstrncmp_assert_for_not_equal_goal25
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal25:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = t_1 a_3; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a_2; x_3 :: int = to_uint8 x_2; x_4 :: int = offset a_1; x_5 :: int = offset a_2; x_6 :: int = offset a; x_7 :: int = offset a_3; x_9 :: int = i_2 + x_5 - x_6; x_10 :: int = l_strnlen t_1 a x_9; x_11 :: int = x_6 + x_10; x_12 :: int = l_strnlen t_1 a_1 x_9; x_13 :: int = x_6 + x_12; x_14 :: int = x_5 - x_6; x_15 :: int = t_1 (shift a_1 x_14); x_16 :: int = t_1 (shift a x_14) in \<not>i_2 = (0 :: int) \<longrightarrow> \<not>x_1 = x_3 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = t_1 (shift a i_1) \<longrightarrow> x_4 + x_5 = x_6 + x_7 \<longrightarrow> x_11 = x_5 + l_strnlen t_1 a_2 i_2 \<longrightarrow> x_4 + x_12 = x_7 + l_strnlen t_1 a_3 i_2 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> x_6 \<le> x_5 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_6 < i_2 + x_5 \<longrightarrow> i_1 < x_12 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint64 i_2 \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_strn t t_1 a_2 i_2 \<longrightarrow> p_valid_strn t t_1 a_3 i_2 \<longrightarrow> is_uint64 x_9 \<longrightarrow> p_valid_strn t t_1 a x_9 \<longrightarrow> p_valid_strn t t_1 a_1 x_9 \<longrightarrow> addr_le a_2 (shift a x_10) \<longrightarrow> addr_le a_3 (shift a_1 x_12) \<longrightarrow> (if x_1 < x_3 then i = -(1 :: int) else i = (1 :: int)) \<longrightarrow> (x_3 = (0 :: int) \<longrightarrow> x_10 = l_strlen t_1 a \<and> x_11 = x_5 \<and> p_valid_str t t_1 a) \<longrightarrow> (x_1 = (0 :: int) \<longrightarrow> x_12 = l_strlen t_1 a_1 \<and> x_13 = x_5 \<and> p_valid_str t t_1 a_1) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 + x_6 < x_5 \<longrightarrow> t_1 (shift a_1 i_3) = t_1 (shift a i_3)) \<longrightarrow> (\<forall>(i_3 :: int). let x_17 :: int = t_1 (shift a_1 i_3); x_18 :: int = t_1 (shift a i_3) in (0 :: int) \<le> i_3 \<longrightarrow> i_3 < x_12 \<longrightarrow> to_uint8 x_17 = to_uint8 x_18 \<longleftrightarrow> x_17 = x_18) \<longrightarrow> \<not>x_15 = x_16 \<and> x_6 + to_uint64 x_14 = x_5 \<and> x_5 < x_13 \<and> (if to_uint8 x_15 < to_uint8 x_16 then i = -(1 :: int) else i = (1 :: int))"
  sorry
end
