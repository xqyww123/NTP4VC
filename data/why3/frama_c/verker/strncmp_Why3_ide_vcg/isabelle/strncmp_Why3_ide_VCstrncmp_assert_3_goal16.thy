theory strncmp_Why3_ide_VCstrncmp_assert_3_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal16:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_1; x_1 :: int = offset a; x_2 :: int = i + x_1; x_3 :: int = offset a_1; x_4 :: int = offset a_2; x_5 :: int = offset a_3; x_6 :: int = i + x_1 - x_3; x_7 :: int = l_strnlen t_1 a i; x_8 :: int = x_1 + x_7; x_9 :: int = l_strnlen t_1 a_2 i; x_10 :: int = t_1 a_3 in to_uint8 x = (0 :: int) \<longrightarrow> \<not>x_2 = x_3 \<longrightarrow> x_3 + x_4 = x_1 + x_5 \<longrightarrow> x_3 + l_strnlen t_1 a_1 x_6 = x_8 \<longrightarrow> x_5 + l_strnlen t_1 a_3 x_6 = x_4 + x_9 \<longrightarrow> x_1 \<le> x_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x_3 \<le> x_2 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> is_sint8 x \<longrightarrow> is_sint8 x_10 \<longrightarrow> p_valid_strn t t_1 a i \<longrightarrow> p_valid_strn t t_1 a_2 i \<longrightarrow> is_uint64 x_6 \<longrightarrow> addr_le a_1 (shift a x_7) \<longrightarrow> addr_le a_3 (shift a_2 x_9) \<longrightarrow> p_valid_strn t t_1 a_1 x_6 \<longrightarrow> p_valid_strn t t_1 a_3 x_6 \<longrightarrow> (to_uint8 x_10 = (0 :: int) \<longrightarrow> x_9 = l_strlen t_1 a_2 \<and> x_1 + x_9 = x_3 \<and> p_valid_str t t_1 a_2) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_1 < x_3 \<longrightarrow> t_1 (shift a_2 i_1) = t_1 (shift a i_1)) \<longrightarrow> (\<forall>(i_1 :: int). let x_11 :: int = t_1 (shift a_2 i_1); x_12 :: int = t_1 (shift a i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_9 \<longrightarrow> to_uint8 x_11 = to_uint8 x_12 \<longleftrightarrow> x_11 = x_12) \<longrightarrow> x_7 = l_strlen t_1 a \<and> x_8 = x_3 \<and> p_valid_str t t_1 a"
  sorry
end
