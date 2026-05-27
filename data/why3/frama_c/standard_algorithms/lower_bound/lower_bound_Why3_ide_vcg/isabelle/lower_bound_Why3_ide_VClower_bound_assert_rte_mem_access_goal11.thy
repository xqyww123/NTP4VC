theory lower_bound_Why3_ide_VClower_bound_assert_rte_mem_access_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_lower_bound_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_lower_bound_lib.Compound_Compound"
begin
theorem goal11:
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = i_1 - i_3; x_1 :: int = i_3 + to_uint32 (to_uint32 x cdiv (2 :: int)); x_2 :: int = i_3 + x cdiv (2 :: int) in i_3 \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> i_1 \<le> (4294967295 :: int) + i_3 \<longrightarrow> x_1 \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_2 \<longrightarrow> p_lowerbound_1' t_1 a i_1 i_2 i \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_3 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_2 \<longrightarrow> is_uint32 x_2 \<longrightarrow> valid_rd t (shift a x_2) (1 :: int)"
  sorry
end
