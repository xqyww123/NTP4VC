theory strncat_Why3_ide_VCstrncat_loop_inv_5_established_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal11:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a; a_2 :: addr = shift a x; x_1 :: int = l_strnlen t_1 a_1 i; x_2 :: int = t_1 (shift a_1 x_1) in \<not>i = (0 :: int) \<longrightarrow> t_1 a_2 = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i + x \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> is_uint64 x \<longrightarrow> p_valid_strn t t_1 a_1 i \<longrightarrow> is_uint64 x_1 \<longrightarrow> addr_le a a_2 \<longrightarrow> addr_le a_2 a_2 \<longrightarrow> is_sint8 x_2 \<longrightarrow> p_valid_str t t_1 a_2 \<longrightarrow> valid_rw t (shift a (0 :: int)) ((1 :: int) + i + x) \<longrightarrow> ((\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int)) \<longrightarrow> x_1 = i) \<longrightarrow> ((\<exists>(i_1 :: int). t_1 (shift a_1 i_1) = (0 :: int) \<and> (0 :: int) \<le> i_1 \<and> i_1 \<le> i) \<longrightarrow> x_2 = (0 :: int)) \<longrightarrow> ((\<exists>(i_1 :: int). t_1 (shift a_1 i_1) = (0 :: int) \<and> (0 :: int) \<le> i_1 \<and> i_1 \<le> i) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x_1 \<longrightarrow> \<not>t_1 (shift a_1 i_1) = (0 :: int))) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> \<not>t_1 (shift a i_1) = (0 :: int)) \<longrightarrow> addr_le a_2 (shift a (x + x_1))"
  sorry
end
