theory PartialSumStep_Why3_ide_VCPartialSumStep_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_adjacent_difference_inv_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_inv_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_adjacent_difference_inv_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_inv_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes t :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes a_1 :: "addr"
  shows "let x :: int = t (shift a i); x_1 :: int = (1 :: int) + i in x = l_accumulate_1' t a_1 x_1 (0 :: int) \<longrightarrow> (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> is_uint32 i \<longrightarrow> p_partialsum t a_1 i a \<longrightarrow> is_sint32 x \<longrightarrow> p_partialsum t a_1 x_1 a"
  sorry
end
