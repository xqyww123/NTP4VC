theory PositiveCountImpliesHasValue_Why3_ide_VCPositiveCountImpliesHasValue_loop_inv_2_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "i_2 < i_1"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "(0 :: int) < l_count_1' t a i_2 i_1 i"
  assumes fact3: "is_uint32 i_1"
  assumes fact4: "is_uint32 i_2"
  assumes fact5: "is_sint32 i"
  shows "l_count_1' t a i_2 i_2 i = (0 :: int)"
  sorry
end
