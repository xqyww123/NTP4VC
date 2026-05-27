theory is_heap_Why3_ide_VCis_heap_loop_inv_heap_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_is_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_heap_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i"
  assumes fact3: "valid_rd t (shift a (0 :: int)) i"
  shows "p_isheap t_1 a (1 :: int)"
  sorry
end
