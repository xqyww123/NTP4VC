theory partial_sum_inv_Why3_ide_VCpartial_sum_inv_post_unchanged_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sum_inv_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sum_inv_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sum_inv_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "frama_c_standard_algorithms_partial_sum_inv_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_partial_sum_inv_lib.Axiomatic2_Axiomatic2" "frama_c_standard_algorithms_partial_sum_inv_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic"
begin
theorem goal0:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 t_3 a_2 i; a_5 :: addr \<Rightarrow> int = havoc t_2 a_4 a_3 i in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rd t a_3 i \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> p_accumulatebounds_1' t_3 a_1 ((1 :: int) + i) (0 :: int) \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> p_adjacentdifferencebounds a_4 a i \<longrightarrow> p_unchanged_1' a_4 t_3 a_1 (0 :: int) i \<longrightarrow> p_partialsum a_4 a_1 i a \<longrightarrow> p_unchanged_1' a_5 a_4 a (0 :: int) i \<longrightarrow> p_adjacentdifference a_5 a i a_1 \<longrightarrow> p_unchanged_1' a_5 t_3 a_1 (0 :: int) i"
  sorry
end
