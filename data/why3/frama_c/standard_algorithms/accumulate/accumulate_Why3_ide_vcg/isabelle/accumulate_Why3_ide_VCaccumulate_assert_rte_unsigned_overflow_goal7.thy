theory accumulate_Why3_ide_VCaccumulate_assert_rte_unsigned_overflow_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_accumulate_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_accumulate_lib.Compound_Compound" "frama_c_standard_algorithms_accumulate_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_accumulate_lib.Axiomatic1_Axiomatic1"
begin
theorem goal7:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_accumulate t_1 a i_2 i_1; a_1 :: addr = shift a i_2; x_1 :: int = t_1 a_1; x_2 :: int = x_1 + x in i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> -(2147483648 :: int) \<le> x_2 \<longrightarrow> x_2 \<le> (2147483647 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_1 \<longrightarrow> p_accumulatebounds_1' t_1 a i i_1 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint32 x \<longrightarrow> i_2 \<le> (4294967294 :: int)"
  sorry
end
