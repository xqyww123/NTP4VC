theory strncmp_Why3_ide_VCstrncmp_equal_post_goal21
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal21:
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes i :: "int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a_2; x_2 :: int = offset a; x_3 :: int = offset a_3; x_4 :: int = i_1 + x_2 - x; x_5 :: int = l_strnlen t_1 a i_1; x_6 :: int = x_2 + x_5; x_7 :: int = l_strnlen t_1 a_2 i_1; x_8 :: int = i_1 + x_2 in x + x_1 = x_2 + x_3 \<longrightarrow> x + l_strnlen t_1 a_1 x_4 = x_6 \<longrightarrow> x_3 + l_strnlen t_1 a_3 x_4 = x_1 + x_7 \<longrightarrow> x_2 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> x \<le> x_8 \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_2 \<longrightarrow> is_uint8 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> addr_le a a_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> p_valid_strn t t_1 a i_1 \<longrightarrow> p_valid_strn t t_1 a_2 i_1 \<longrightarrow> is_uint64 x_4 \<longrightarrow> addr_le a_1 (shift a x_5) \<longrightarrow> addr_le a_3 (shift a_2 x_7) \<longrightarrow> p_valid_strn t t_1 a_1 x_4 \<longrightarrow> p_valid_strn t t_1 a_3 x_4 \<longrightarrow> (if x_8 = x then i = (0 :: int) else to_uint8 (t_1 a_1) = i_2 \<and> to_uint8 (t_1 a_3) = i_3 \<and> (if i_3 = i_2 then i = (0 :: int) \<and> i_3 = (0 :: int) else if i_3 < i_2 then i = -(1 :: int) else i = (1 :: int)) \<and> (i_2 = (0 :: int) \<longrightarrow> x_5 = l_strlen t_1 a \<and> x_6 = x \<and> p_valid_str t t_1 a) \<and> (i_3 = (0 :: int) \<longrightarrow> x_7 = l_strlen t_1 a_2 \<and> x_2 + x_7 = x \<and> p_valid_str t t_1 a_2)) \<longrightarrow> i_1 = (0 :: int) \<or> x_7 = x_5 \<and> (0 :: int) < i_1 \<and> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_7 \<longrightarrow> t_1 (shift a_2 i_4) = t_1 (shift a i_4)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + x_2 < x \<longrightarrow> t_1 (shift a_2 i_4) = t_1 (shift a i_4)) \<longrightarrow> (\<forall>(i_4 :: int). let x_9 :: int = t_1 (shift a_2 i_4); x_10 :: int = t_1 (shift a i_4) in (0 :: int) \<le> i_4 \<longrightarrow> i_4 < x_7 \<longrightarrow> to_uint8 x_9 = to_uint8 x_10 \<longleftrightarrow> x_9 = x_10) \<longrightarrow> i = (0 :: int)"
  sorry
end
