theory strcasecmp_Why3_ide_VCstrcasecmp_loop_inv_3_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Ctype_A_Ctype" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal3:
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let x :: int = t_2 a; x_1 :: int = l_tolower x; x_2 :: int = t_1 a_1; x_3 :: int = offset a_1; x_4 :: int = offset a_3; a_4 :: addr = shift a (1 :: int) in \<not>x_1 = (0 :: int) \<longrightarrow> x_1 = l_tolower x_2 \<longrightarrow> x_3 + offset a_2 = offset a + x_4 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_sint8 x_1 \<longrightarrow> is_sint32 x_1 \<longrightarrow> addr_le a (shift a_2 (l_strlen t_1 a_2)) \<longrightarrow> addr_le a_1 (shift a_3 (l_strlen t_1 a_3)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i + x_4 < x_3 \<longrightarrow> l_tolower (t_1 (shift a_3 i)) = l_tolower (t_1 (shift a_2 i))) \<longrightarrow> addr_le a_2 a_4 \<and> addr_le a_4 (shift a_2 (l_strlen t_3 a_2))"
  sorry
end
