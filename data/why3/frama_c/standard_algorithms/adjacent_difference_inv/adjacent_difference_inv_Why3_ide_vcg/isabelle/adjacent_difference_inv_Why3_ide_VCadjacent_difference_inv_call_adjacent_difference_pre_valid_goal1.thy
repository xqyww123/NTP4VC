theory adjacent_difference_inv_Why3_ide_VCadjacent_difference_inv_call_adjacent_difference_pre_valid_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_inv_lib.Axiomatic2_Axiomatic2" "frama_c_standard_algorithms_adjacent_difference_inv_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic" "frama_c_standard_algorithms_adjacent_difference_inv_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_inv_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> p_adjacentdifferencebounds t_1 a_1 ((1 :: int) + i) \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> valid_rd t a_3 i"
  sorry
end
