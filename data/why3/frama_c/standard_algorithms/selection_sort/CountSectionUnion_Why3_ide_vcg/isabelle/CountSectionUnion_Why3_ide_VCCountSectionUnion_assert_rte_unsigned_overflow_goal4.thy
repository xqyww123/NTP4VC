theory CountSectionUnion_Why3_ide_VCCountSectionUnion_assert_rte_unsigned_overflow_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_selection_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_selection_sort_lib.Compound_Compound" "frama_c_standard_algorithms_selection_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i"
  assumes fact1: "i_3 \<le> i"
  assumes fact2: "i_1 \<le> i_2"
  assumes fact3: "i_3 < i"
  assumes fact4: "i_2 \<le> i_3"
  assumes fact5: "region (base a) \<le> (0 :: int)"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_uint32 i_1"
  assumes fact8: "is_uint32 i_2"
  assumes fact9: "is_uint32 i_3"
  assumes fact10: "\<forall>(i_4 :: int). is_sint32 i_4 \<longrightarrow> l_count_1' t a i_1 i_2 i_4 + l_count_1' t a i_2 i_3 i_4 = l_count_1' t a i_1 i_3 i_4"
  shows "i_3 \<le> (4294967294 :: int)"
  sorry
end
