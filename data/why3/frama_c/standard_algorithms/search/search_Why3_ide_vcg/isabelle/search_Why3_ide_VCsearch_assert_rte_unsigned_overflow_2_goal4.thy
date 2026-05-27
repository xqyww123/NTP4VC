theory search_Why3_ide_VCsearch_assert_rte_unsigned_overflow_2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_search_lib.Compound_Compound" "frama_c_standard_algorithms_search_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i \<le> i_1"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "region (base a_1) \<le> (0 :: int)"
  assumes fact3: "i + i_2 \<le> (1 :: int) + i_1"
  assumes fact4: "linked t"
  assumes fact5: "is_uint32 i"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "is_uint32 i_2"
  assumes fact8: "valid_rd t (shift a (0 :: int)) i"
  assumes fact9: "valid_rd t (shift a_1 (0 :: int)) i_1"
  assumes fact10: "\<not>p_hassubrange_1' t_1 a_1 (0 :: int) (i + i_2 - (1 :: int)) a i"
  shows "i_1 \<le> (4294967295 :: int) + i"
  sorry
end
