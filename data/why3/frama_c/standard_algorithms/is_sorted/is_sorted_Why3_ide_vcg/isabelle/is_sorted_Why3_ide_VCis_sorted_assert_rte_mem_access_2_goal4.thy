theory is_sorted_Why3_ide_VCis_sorted_assert_rte_mem_access_2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_1 in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) + i_1 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> p_weaklysorted_1' t_1 a (0 :: int) x \<longrightarrow> valid_rd t (shift a (to_uint32 x)) (1 :: int)"
  sorry
end
