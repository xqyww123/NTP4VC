theory adjacent_difference_Why3_ide_VCadjacent_difference_assert_rte_mem_access_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_adjacent_difference_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int) in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> p_adjacentdifferencebounds t_1 a_1 i \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> valid_rw t a_3 (1 :: int)"
  sorry
end
