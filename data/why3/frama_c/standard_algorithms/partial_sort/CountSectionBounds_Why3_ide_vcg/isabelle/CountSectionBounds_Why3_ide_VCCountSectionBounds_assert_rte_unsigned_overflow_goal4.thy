theory CountSectionBounds_Why3_ide_VCCountSectionBounds_assert_rte_unsigned_overflow_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 \<le> i"
  assumes fact1: "i_2 \<le> i"
  assumes fact2: "i_2 < i"
  assumes fact3: "i_1 \<le> i_2"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "is_uint32 i"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "is_uint32 i_2"
  assumes fact8: "\<forall>(i_3 :: int). let x :: int = l_count_1' t a i_1 i_2 i_3 in is_sint32 i_3 \<longrightarrow> (0 :: int) \<le> x \<and> i_1 + x \<le> i_2"
  shows "i_2 \<le> (4294967294 :: int)"
  sorry
end
