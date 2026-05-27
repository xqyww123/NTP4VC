theory accumulate_Why3_ide_VCaccumulate_assert_rte_mem_access_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_accumulate_lib.A_AccumulateAxiomatic_A_AccumulateAxiomatic" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_accumulate_lib.Compound_Compound" "frama_c_standard_algorithms_accumulate_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_accumulate_lib.Axiomatic1_Axiomatic1"
begin
theorem goal4:
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i"
  assumes fact1: "(0 :: int) \<le> i_2"
  assumes fact2: "i_2 < i"
  assumes fact3: "region (base a) \<le> (0 :: int)"
  assumes fact4: "linked t"
  assumes fact5: "is_uint32 i"
  assumes fact6: "is_uint32 i_2"
  assumes fact7: "is_sint32 i_1"
  assumes fact8: "p_accumulatebounds_1' t_1 a i i_1"
  assumes fact9: "valid_rd t (shift a (0 :: int)) i"
  assumes fact10: "is_sint32 (l_accumulate t_1 a i_2 i_1)"
  shows "valid_rd t (shift a i_2) (1 :: int)"
  sorry
end
