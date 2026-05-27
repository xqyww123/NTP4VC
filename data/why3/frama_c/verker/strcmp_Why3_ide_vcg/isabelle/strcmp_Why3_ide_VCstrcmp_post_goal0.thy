theory strcmp_Why3_ide_VCstrcmp_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_StrCmp_A_StrCmp" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_3 :: "addr"
  fixes a_1 :: "addr"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes p :: "bool"
  fixes p_1 :: "bool"
  fixes i_2 :: "int"
  fixes i :: "int"
  shows "let x :: int = l_strcmp t_1 a_3 a_1; x_1 :: int = offset a_2; x_2 :: int = offset a_3; x_3 :: int = l_strlen t_1 a_3; x_4 :: int = x_2 + x_3; x_5 :: int = t_1 a; x_6 :: int = t_1 a_2; x_7 :: int = to_uint8 x_6; x_8 :: int = to_uint8 x_5; x_9 :: int = x_1 - x_2; x_10 :: int = t_1 (shift a_3 x_9); x_11 :: int = t_1 (shift a_1 x_9) in x = l_strcmp t_1 a_2 a \<longrightarrow> offset a_1 + x_1 = offset a + x_2 \<longrightarrow> x_4 = x_1 + l_strlen t_1 a_2 \<longrightarrow> ((\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 \<le> x_3 \<longrightarrow> to_uint8 (t_1 (shift a_3 i_4)) = to_uint8 (t_1 (shift a_1 i_4))) \<longleftrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 \<le> x_3 \<longrightarrow> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4))) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint8 i_3 \<longrightarrow> is_sint32 i_1 \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_3 a_2 \<longrightarrow> is_sint8 x_5 \<longrightarrow> is_sint8 x_6 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> addr_le a (shift a_1 (l_strlen t_1 a_1)) \<longrightarrow> addr_le a_2 (shift a_3 x_3) \<longrightarrow> (if x_7 = x_8 then i_1 = (0 :: int) \<and> x_7 = (0 :: int) else p = False \<and> p_1 = False \<and> i_2 = i \<and> x_7 = i_3 \<and> \<not>x_10 = x_11 \<and> x_2 \<le> x_1 \<and> x_1 \<le> x_4 \<and> (if i_3 < x_8 then i_1 = -(1 :: int) else i_1 = (1 :: int)) \<and> (if i_3 < x_8 then i_2 = -(1 :: int) else i_2 = (1 :: int)) \<and> (if to_uint8 x_10 < to_uint8 x_11 then i_2 = -(1 :: int) else i_2 = (1 :: int))) \<longrightarrow> (\<forall>(i_4 :: int). (0 :: int) \<le> i_4 \<longrightarrow> i_4 + x_2 < x_1 \<longrightarrow> t_1 (shift a_3 i_4) = t_1 (shift a_1 i_4)) \<longrightarrow> x = i_1"
  sorry
end
