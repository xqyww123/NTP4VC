theory check_bytes8_Why3_ide_VCcheck_bytes8_assert_2_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_CheckBytes8_A_CheckBytes8" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal9:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = offset a; x_1 :: int = offset a_1; x_2 :: int = x - x_1; a_2 :: addr = l_check_bytes8 t_1 a_1 i x_2 in a_2 = l_check_bytes8 t_1 a i (0 :: int) \<longrightarrow> x_1 \<le> x \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint8 i \<longrightarrow> addr_le a_1 a \<longrightarrow> is_uint32 x_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_2 \<longrightarrow> addr_le a (shift a_1 x_2) \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> t_1 a_3 = i) \<longrightarrow> a_2 = Mk_addr (0 :: int) (0 :: int)"
  sorry
end
