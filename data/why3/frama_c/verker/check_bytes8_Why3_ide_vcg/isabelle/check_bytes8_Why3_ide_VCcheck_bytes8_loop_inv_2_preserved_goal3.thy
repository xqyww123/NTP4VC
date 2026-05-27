theory check_bytes8_Why3_ide_VCcheck_bytes8_loop_inv_2_preserved_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_CheckBytes8_A_CheckBytes8" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal3:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a_1; x_1 :: int = i + x; x_2 :: int = offset a; x_3 :: int = t_1 a; x_4 :: int = i + x - x_2; a_2 :: addr = shift a_1 i; a_3 :: addr = shift a (1 :: int) in \<not>x_1 = x_2 \<longrightarrow> l_check_bytes8 t_1 a x_3 x_4 = l_check_bytes8 t_1 a_1 x_3 i \<longrightarrow> x \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_uint8 x_3 \<longrightarrow> addr_le a a_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> is_uint32 x_4 \<longrightarrow> (\<forall>(a_4 :: addr). addr_lt a_4 a \<longrightarrow> addr_le a_1 a_4 \<longrightarrow> x_3 = t_1 a_4) \<longrightarrow> addr_le a_1 a_3 \<and> addr_le a_3 a_2"
  sorry
end
