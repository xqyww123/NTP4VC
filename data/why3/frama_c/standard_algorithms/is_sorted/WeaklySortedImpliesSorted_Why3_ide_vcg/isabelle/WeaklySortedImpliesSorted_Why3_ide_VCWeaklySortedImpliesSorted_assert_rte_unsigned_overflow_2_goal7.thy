theory WeaklySortedImpliesSorted_Why3_ide_VCWeaklySortedImpliesSorted_assert_rte_unsigned_overflow_2_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound"
begin
theorem goal7:
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i"
  assumes fact1: "i_3 \<le> i"
  assumes fact2: "i_2 \<le> i_1"
  assumes fact3: "i_1 \<le> i_2"
  assumes fact4: "i_3 < i"
  assumes fact5: "i_1 \<le> i_3"
  assumes fact6: "i_2 \<le> i_3"
  assumes fact7: "region (base a) \<le> (0 :: int)"
  assumes fact8: "is_uint32 i"
  assumes fact9: "is_uint32 i_1"
  assumes fact10: "is_uint32 i_2"
  assumes fact11: "is_uint32 i_3"
  assumes fact12: "p_sorted_1' t a i_2 i_3"
  assumes fact13: "p_weaklysorted_1' t a i_2 i"
  assumes fact14: "\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> t (shift a i_4) \<le> t (shift a i_3)"
  shows "i_3 \<le> (4294967294 :: int)"
  sorry
end
