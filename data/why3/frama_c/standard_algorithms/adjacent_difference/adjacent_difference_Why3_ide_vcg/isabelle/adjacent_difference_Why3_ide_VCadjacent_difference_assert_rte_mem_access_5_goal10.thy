theory adjacent_difference_Why3_ide_VCadjacent_difference_assert_rte_mem_access_5_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_adjacent_difference_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 (t_2(a_3 := t_2 a_2)) (shift a (1 :: int)) (i - (1 :: int)) in (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_adjacentdifferencebounds t_2 a_1 i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> p_unchanged_1' a_4 t_2 a_1 (0 :: int) i \<longrightarrow> p_adjacentdifference a_4 a_1 i_1 a \<longrightarrow> valid_rd t (shift a_1 (to_uint32 (i_1 - (1 :: int)))) (1 :: int)"
  sorry
end
