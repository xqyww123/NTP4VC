theory HeapMaximum_Why3_ide_VCHeapMaximum_assert_rte_unsigned_overflow_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "i_1 \<le> i"
  assumes fact2: "(0 :: int) \<le> i_1"
  assumes fact3: "i_1 < i"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "is_uint32 i"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "p_isheap t a i"
  assumes fact8: "\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> t (shift a i_2) \<le> t (shift a (0 :: int))"
  shows "i_1 \<le> (4294967294 :: int)"
  sorry
end
