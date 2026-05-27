theory adjacent_find_Why3_ide_VCadjacent_find_loop_inv_none_established_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_find_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_find_lib.Axiomatic_Axiomatic"
begin
theorem goal4:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "(2 :: int) \<le> i"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i"
  shows "\<not>p_hasequalneighbors t_1 a (1 :: int)"
  sorry
end
