theory strcat_Why3_ide_VCstrcat_loop_inv_3_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a_2; x_1 :: int = l_strlen t_1 a; a_3 :: addr = shift a x_1; x_2 :: int = offset a; x_3 :: int = offset a_2; x_4 :: int = l_strlen t_1 a_1 in \<not>x = (0 :: int) \<longrightarrow> t_1 a_3 = (0 :: int) \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i + x_2 \<le> x_3 \<longrightarrow> x_1 + x_4 \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> is_sint8 x \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> is_uint64 x_1 \<longrightarrow> addr_le a_2 a_3 \<longrightarrow> valid_rw t (shift a (0 :: int)) ((1 :: int) + x_1 + x_4) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_1 \<longrightarrow> \<not>t_1 (shift a i_1) = (0 :: int)) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 + x_2 < x_3 \<longrightarrow> \<not>t_1 (shift a i_1) = (0 :: int)) \<longrightarrow> \<not>t_1 (shift a i) = (0 :: int)"
  sorry
end
