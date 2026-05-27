theory partial_sum_Why3_ide_VCpartial_sum_loop_inv_accumulate_established_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sum_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sum_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sum_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "frama_c_standard_algorithms_partial_sum_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); x :: int = t_1 a_2; a_3 :: addr = shift a (0 :: int) in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> valid_rw t a_3 i \<longrightarrow> p_accumulatebounds_1' t_1 a_1 ((1 :: int) + i) (0 :: int) \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> x = l_accumulate_1' (t_1(a_3 := x)) a_1 (1 :: int) (0 :: int)"
  sorry
end
