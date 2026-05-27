theory insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_bound_established_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_insertion_sort_lib.Compound_Compound"
begin
theorem goal3:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i"
  assumes fact3: "valid_rw t (shift a (0 :: int)) i"
  shows "(0 :: int) \<le> i"
  sorry
end
