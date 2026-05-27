theory PositiveCountImpliesHasValue_Why3_ide_VCPositiveCountImpliesHasValue_assert_rte_unsigned_overflow_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "i_3 \<le> i_1"
  assumes fact1: "i_2 < i_1"
  assumes fact2: "i_3 < i_1"
  assumes fact3: "i_2 \<le> i_3"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "(0 :: int) < l_count_1' t a i_2 i_1 i"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "is_uint32 i_2"
  assumes fact8: "is_uint32 i_3"
  assumes fact9: "is_sint32 i"
  assumes fact10: "(\<forall>(i_4 :: int). i_2 \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> \<not>t (shift a i_4) = i) \<longrightarrow> l_count_1' t a i_2 i_3 i = (0 :: int)"
  shows "i_3 \<le> (4294967294 :: int)"
  sorry
end
