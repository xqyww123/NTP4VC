theory adjacent_find_Why3_ide_VCadjacent_find_loop_inv_bound_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_find_lib.Compound_Compound"
begin
theorem goal2:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "(2 :: int) \<le> i"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i"
  shows "(0 :: int) < i"
  sorry
end
