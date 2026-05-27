theory strcmp_Why3_ide_VCstrcmp_not_equal_post_2_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCmp_A_StrCmp" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal17:
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  shows "let x :: int = offset a_2; x_1 :: int = offset a_3; x_2 :: int = l_strlen t_1 a_3; x_3 :: int = x_1 + x_2; x_4 :: int = t_1 a; x_5 :: int = t_1 a_2; x_6 :: int = to_uint8 x_5; x_7 :: int = to_uint8 x_4; x_8 :: int = x - x_1; x_9 :: int = t_1 (shift a_3 x_8); x_10 :: int = t_1 (shift a_1 x_8) in l_strcmp t_1 a_3 a_1 = l_strcmp t_1 a_2 a \<longrightarrow> \<not>t_1 (shift a_3 i_3) = t_1 (shift a_1 i_3) \<longrightarrow> offset a_1 + x = offset a + x_1 \<longrightarrow> x_3 = x + l_strlen t_1 a_2 \<longrightarrow> ((\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 \<le> x_2 \<longrightarrow> to_uint8 (t_1 (shift a_3 i_5)) = to_uint8 (t_1 (shift a_1 i_5))) \<longleftrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 \<le> x_2 \<longrightarrow> t_1 (shift a_3 i_5) = t_1 (shift a_1 i_5))) \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_4 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> is_sint8 x_4 \<longrightarrow> is_sint8 x_5 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_le a (shift a_1 (l_strlen t_1 a_1)) \<longrightarrow> addr_le a_2 (shift a_3 x_2) \<longrightarrow> (if x_6 = x_7 then i_1 = (0 :: int) \<and> x_6 = (0 :: int) else i_2 = i \<and> x_6 = i_4 \<and> \<not>x_9 = x_10 \<and> x_1 \<le> x \<and> x \<le> x_3 \<and> (if i_4 < x_7 then i_1 = -(1 :: int) else i_1 = (1 :: int)) \<and> (if i_4 < x_7 then i_2 = -(1 :: int) else i_2 = (1 :: int)) \<and> (if to_uint8 x_9 < to_uint8 x_10 then i_2 = -(1 :: int) else i_2 = (1 :: int))) \<longrightarrow> (\<forall>(i_5 :: int). (0 :: int) \<le> i_5 \<longrightarrow> i_5 + x_1 < x \<longrightarrow> t_1 (shift a_3 i_5) = t_1 (shift a_1 i_5)) \<longrightarrow> (\<exists>(i_5 :: int). let x_11 :: int = t_1 (shift a_3 i_5); x_12 :: int = t_1 (shift a_1 i_5) in \<not>x_11 = x_12 \<and> (0 :: int) \<le> i_5 \<and> i_5 \<le> x_2 \<and> (if to_uint8 x_11 < to_uint8 x_12 then i_1 = -(1 :: int) else i_1 = (1 :: int)) \<and> (\<forall>(i_6 :: int). (0 :: int) \<le> i_6 \<longrightarrow> i_6 < i_5 \<longrightarrow> t_1 (shift a_3 i_6) = t_1 (shift a_1 i_6)))"
  sorry
end
