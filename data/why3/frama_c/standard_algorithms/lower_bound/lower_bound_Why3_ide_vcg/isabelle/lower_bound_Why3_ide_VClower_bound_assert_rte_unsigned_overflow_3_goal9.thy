theory lower_bound_Why3_ide_VClower_bound_assert_rte_unsigned_overflow_3_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_lower_bound_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_lower_bound_lib.Compound_Compound"
begin
theorem goal9:
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "i_3 \<le> i_1"
  assumes fact1: "i_1 \<le> i_2"
  assumes fact2: "(0 :: int) \<le> i_3"
  assumes fact3: "i_3 < i_1"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "linked t"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "is_uint32 i_2"
  assumes fact8: "is_uint32 i_3"
  assumes fact9: "is_sint32 i"
  assumes fact10: "p_sorted_1' t_1 a (0 :: int) i_2"
  assumes fact11: "p_lowerbound_1' t_1 a i_1 i_2 i"
  assumes fact12: "p_strictupperbound_1' t_1 a (0 :: int) i_3 i"
  assumes fact13: "valid_rd t (shift a (0 :: int)) i_2"
  shows "(0 :: int) \<le> i_3 + to_uint32 (to_uint32 (i_1 - i_3) cdiv (2 :: int))"
  sorry
end
