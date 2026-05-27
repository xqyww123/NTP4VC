theory maximum_heap_child_Why3_ide_VCmaximum_heap_child_assert_rte_unsigned_overflow_3_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_pop_heap_lib.Compound_Compound"
begin
theorem goal4:
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "(2 :: int) \<le> i_1"
  assumes fact3: "i \<le> (2147483646 :: int)"
  assumes fact4: "(2 :: int) + i \<le> i_1"
  assumes fact5: "linked t"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_uint32 i_1"
  assumes fact8: "p_isheap t_1 a i_1"
  assumes fact9: "valid_rw t (shift a (0 :: int)) i_1"
  shows "to_uint32 ((2 :: int) * i) \<le> (4294967293 :: int)"
  sorry
end
