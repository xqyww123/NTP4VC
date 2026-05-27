theory strcasecmp_Why3_ide_VCstrcasecmp_loop_assign_part6_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Ctype_A_Ctype" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal9:
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = offset a_3; x_2 :: int = t_1 a_1 in x + offset a_2 = offset a + x_1 \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> region (base a_3) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a_2 a \<longrightarrow> addr_le a_3 a_1 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> p_valid_str t t_1 a_3 \<longrightarrow> is_sint8 (l_tolower x_2) \<longrightarrow> addr_le a (shift a_2 (l_strlen t_1 a_2)) \<longrightarrow> addr_le a_1 (shift a_3 (l_strlen t_1 a_3)) \<longrightarrow> \<not>(\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i + x_1 < x \<longrightarrow> l_tolower (t_1 (shift a_3 i)) = l_tolower (t_1 (shift a_2 i)))"
  sorry
end
