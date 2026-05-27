theory check_bytes8_Why3_ide_VCcheck_bytes8_loop_inv_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_CheckBytes8_A_CheckBytes8" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 a; x_1 :: int = offset a; x_2 :: int = offset a_1; x_3 :: int = i + x_1 - x_2 in \<not>i = (0 :: int) \<longrightarrow> l_check_bytes8 t_1 a_1 x x_3 = l_check_bytes8 t_1 a x i \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_uint8 x \<longrightarrow> is_uint32 x_3 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_3 \<longrightarrow> addr_le a (shift a_1 x_3) \<longrightarrow> (\<forall>(a_2 :: addr). addr_lt a_2 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> x = t_1 a_2) \<longrightarrow> x_2 + to_uint32 (i - (1 :: int)) \<le> i + x_1"
  sorry
end
