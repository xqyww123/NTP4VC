theory strcmp_Why3_ide_VCstrcmp_equal_post_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCmp_A_StrCmp" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal15:
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  shows "let x :: int = offset a_2; x_1 :: int = offset a_3; x_2 :: int = l_strlen t_1 a_3; x_3 :: int = t_1 a; x_4 :: int = t_1 a_2; x_5 :: int = to_uint8 x_4; x_6 :: int = x - x_1; x_7 :: int = t_2 (shift a_3 x_6); x_8 :: int = t_2 (shift a_1 x_6); x_9 :: int = to_uint8 (t_2 a) in l_strcmp t_1 a_3 a_1 = l_strcmp t_1 a_2 a \<longrightarrow> offset a_1 + x = offset a + x_1 \<longrightarrow> x_1 + x_2 = x + l_strlen t_1 a_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_3 \<longrightarrow> is_sint32 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> is_sint8 x_3 \<longrightarrow> is_sint8 x_4 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_le a (shift a_1 (l_strlen t_1 a_1)) \<longrightarrow> addr_le a_2 (shift a_3 x_2) \<longrightarrow> (if x_5 = to_uint8 x_3 then i_1 = (0 :: int) \<and> x_5 = (0 :: int) else i_2 = i \<and> t_2 = t_1 \<and> to_uint8 (t_2 a_2) = i_3 \<and> \<not>x_7 = x_8 \<and> x_1 \<le> x \<and> x \<le> x_1 + l_strlen t_2 a_3 \<and> (if i_3 < x_9 then i_1 = -(1 :: int) else i_1 = (1 :: int)) \<and> (if i_3 < x_9 then i_2 = -(1 :: int) else i_2 = (1 :: int)) \<and> (if to_uint8 x_7 < to_uint8 x_8 then i_2 = -(1 :: int) else i_2 = (1 :: int)) \<and> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + x_1 < x \<longrightarrow> t_2 (shift a_3 i_4) = t_2 (shift a_1 i_4))) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 \<le> x_2 \<longrightarrow> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + x_1 < x \<longrightarrow> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4)) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 \<le> x_2 \<longrightarrow> to_uint8 (t_1 (shift a_3 i_4)) = to_uint8 (t_1 (shift a_1 i_4))) \<longrightarrow> i_1 = (0 :: int)"
  sorry
end
