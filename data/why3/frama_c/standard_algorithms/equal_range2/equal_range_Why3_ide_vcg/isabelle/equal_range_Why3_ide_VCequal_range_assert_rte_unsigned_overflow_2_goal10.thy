theory equal_range_Why3_ide_VCequal_range_assert_rte_unsigned_overflow_2_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_equal_range2_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_equal_range2_lib.Compound_Compound"
begin
theorem goal10:
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i_1"
  assumes fact1: "i_3 \<le> i_2"
  assumes fact2: "(0 :: int) \<le> i_3"
  assumes fact3: "i_3 < i_2"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "linked t"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "is_uint32 i_2"
  assumes fact8: "is_uint32 i_3"
  assumes fact9: "is_sint32 i"
  assumes fact10: "p_sorted_1' t_1 a (0 :: int) i_1"
  assumes fact11: "p_strictupperbound_1' t_1 a (0 :: int) i_3 i"
  assumes fact12: "p_strictlowerbound_1' t_1 a i_2 i_1 i"
  assumes fact13: "valid_rd t (shift a (0 :: int)) i_1"
  shows "i_2 \<le> (4294967295 :: int) + i_3"
  sorry
end
