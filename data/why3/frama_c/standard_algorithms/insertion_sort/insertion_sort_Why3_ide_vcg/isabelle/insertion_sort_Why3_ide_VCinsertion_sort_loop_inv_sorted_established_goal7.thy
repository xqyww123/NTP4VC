theory insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_sorted_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_insertion_sort_lib.Compound_Compound" "frama_c_standard_algorithms_insertion_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_insertion_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_insertion_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal7:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i"
  assumes fact3: "valid_rw t (shift a (0 :: int)) i"
  shows "p_sorted_1' t_1 a (0 :: int) (0 :: int)"
  sorry
end
