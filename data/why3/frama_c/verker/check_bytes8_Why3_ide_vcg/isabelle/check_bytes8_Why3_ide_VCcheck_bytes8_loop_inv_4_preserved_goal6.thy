theory check_bytes8_Why3_ide_VCcheck_bytes8_loop_inv_4_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_CheckBytes8_A_CheckBytes8" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal6:
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_2 :: "addr"
  shows "let x :: int = offset a_1; x_1 :: int = i + x; x_2 :: int = offset a; x_3 :: int = t_1 a; x_4 :: int = i + x - x_2 in \<not>x_1 = x_2 \<longrightarrow> l_check_bytes8 t_1 a x_3 x_4 = l_check_bytes8 t_1 a_1 x_3 i \<longrightarrow> x \<le> x_2 \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> x_2 \<le> x_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> addr_le a_1 a \<longrightarrow> addr_le a_1 a_2 \<longrightarrow> is_uint8 x_3 \<longrightarrow> addr_lt a_2 (shift a (1 :: int)) \<longrightarrow> addr_le a (shift a_1 i) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> is_uint32 x_4 \<longrightarrow> (\<forall>(a_3 :: addr). addr_lt a_3 a \<longrightarrow> addr_le a_1 a_3 \<longrightarrow> x_3 = t_1 a_3) \<longrightarrow> t_1 a_2 = x_3"
  sorry
end
