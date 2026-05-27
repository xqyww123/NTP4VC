theory equal_range_Why3_ide_VCequal_range_loop_inv_right_established_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_equal_range2_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_equal_range2_lib.Compound_Compound"
begin
theorem goal9:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i_1"
  assumes fact3: "is_sint32 i"
  assumes fact4: "p_sorted_1' t_1 a (0 :: int) i_1"
  assumes fact5: "valid_rd t (shift a (0 :: int)) i_1"
  shows "p_strictlowerbound_1' t_1 a i_1 i_1 i"
  sorry
end
