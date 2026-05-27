theory strcasecmp_Why3_ide_VCstrcasecmp_equal_post_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Ctype_A_Ctype" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal16:
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a_3; x_2 :: int = t_1 a_1; x_3 :: int = t_2 a; x_4 :: int = l_tolower x_2; x_5 :: int = l_tolower x_3; x_6 :: int = l_strlen t_1 a_3; x_7 :: int = x - x_1; x_8 :: int = l_tolower (t_3 (shift a_3 x_7)); x_9 :: int = l_tolower (t_3 (shift a_2 x_7)) in x + offset a_2 = offset a + x_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_sint32 i \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x_3 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_sint8 x_4 \<longrightarrow> is_sint8 x_5 \<longrightarrow> is_sint32 x_4 \<longrightarrow> is_sint32 x_5 \<longrightarrow> addr_le a (shift a_2 (l_strlen t_1 a_2)) \<longrightarrow> addr_le a_1 (shift a_3 x_6) \<longrightarrow> is_sint32 (x_4 - x_5) \<longrightarrow> (if x_5 = x_4 then i = (0 :: int) \<and> x_5 = (0 :: int) else i + x_5 = x_4) \<longrightarrow> (x_5 = x_4 \<longrightarrow> i = (0 :: int) \<and> x_4 = (0 :: int)) \<longrightarrow> (\<not>x_5 = x_4 \<longrightarrow> \<not>x_8 = x_9 \<and> i + x_9 = x_8 \<and> x_1 \<le> x \<and> x \<le> x_1 + l_strlen t_3 a_3 \<and> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_1 < x \<longrightarrow> l_tolower (t_3 (shift a_3 i_1)) = l_tolower (t_3 (shift a_2 i_1)))) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_1 < x \<longrightarrow> l_tolower (t_1 (shift a_3 i_1)) = l_tolower (t_1 (shift a_2 i_1))) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> x_6 \<longrightarrow> l_tolower (t_1 (shift a_3 i_1)) = l_tolower (t_1 (shift a_2 i_1))) \<longrightarrow> x_5 = x_4"
  sorry
end
