theory max_element_Why3_ide_VCmax_element_assert_rte_mem_access_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_max_element_lib.Compound_Compound"
begin
theorem goal6:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_1; x :: int = t_1 a_1 in (0 :: int) < i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 (t_1 (shift a i_2)) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> t_1 (shift a i_3) < x) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> t_1 (shift a i_3) \<le> x) \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
