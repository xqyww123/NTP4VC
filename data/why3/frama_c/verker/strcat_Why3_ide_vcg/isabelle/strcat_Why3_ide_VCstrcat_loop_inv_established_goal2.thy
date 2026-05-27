theory strcat_Why3_ide_VCstrcat_loop_inv_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.Compound_Compound" "frama_c_verker_lib.A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_strlen t_1 a_1; a_2 :: addr = shift a_1 x; x_1 :: int = l_strlen t_1 a in t_1 a_2 = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_1 + x \<le> (18446744073709551615 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> is_uint64 x \<longrightarrow> valid_rw t (shift a_1 (0 :: int)) ((1 :: int) + x_1 + x) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < x \<longrightarrow> \<not>t_1 (shift a_1 i) = (0 :: int)) \<longrightarrow> addr_le a_1 a_1 \<and> addr_le a_1 a_2"
  sorry
end
