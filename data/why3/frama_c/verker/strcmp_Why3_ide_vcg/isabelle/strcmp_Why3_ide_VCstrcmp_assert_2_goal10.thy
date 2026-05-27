theory strcmp_Why3_ide_VCstrcmp_assert_2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCmp_A_StrCmp" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal10:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = t_1 a_2; x_1 :: int = to_uint8 x; x_2 :: int = t_1 a; x_3 :: int = to_uint8 x_2; x_4 :: int = offset a_2; x_5 :: int = offset a_3; x_6 :: int = l_strlen t_1 a_3; x_7 :: int = x_5 + x_6; x_8 :: int = x_4 - x_5; x_9 :: int = t_1 (shift a_3 x_8); x_10 :: int = t_1 (shift a_1 x_8) in \<not>x_1 = x_3 \<longrightarrow> l_strcmp t_1 a_3 a_1 = l_strcmp t_1 a_2 a \<longrightarrow> offset a_1 + x_4 = offset a + x_5 \<longrightarrow> x_7 = x_4 + l_strlen t_1 a_2 \<longrightarrow> ((\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> x_6 \<longrightarrow> to_uint8 (t_1 (shift a_3 i_1)) = to_uint8 (t_1 (shift a_1 i_1))) \<longleftrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> x_6 \<longrightarrow> t_1 (shift a_3 i_1) = t_1 (shift a_1 i_1))) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_le a (shift a_1 (l_strlen t_1 a_1)) \<longrightarrow> addr_le a_2 (shift a_3 x_6) \<longrightarrow> (if x_1 < x_3 then i = -(1 :: int) else i = (1 :: int)) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_5 < x_4 \<longrightarrow> t_1 (shift a_3 i_1) = t_1 (shift a_1 i_1)) \<longrightarrow> \<not>x_9 = x_10 \<and> x_5 \<le> x_4 \<and> x_4 \<le> x_7 \<and> (if to_uint8 x_9 < to_uint8 x_10 then i = -(1 :: int) else i = (1 :: int))"
  sorry
end
