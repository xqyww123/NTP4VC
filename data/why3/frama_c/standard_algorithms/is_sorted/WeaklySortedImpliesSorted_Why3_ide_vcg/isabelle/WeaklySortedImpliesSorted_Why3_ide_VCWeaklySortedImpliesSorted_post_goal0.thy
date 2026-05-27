theory WeaklySortedImpliesSorted_Why3_ide_VCWeaklySortedImpliesSorted_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound"
begin
theorem goal0:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i < i_1"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "is_uint32 i"
  assumes fact3: "is_uint32 i_1"
  assumes fact4: "p_weaklysorted_1' t a i_1 i"
  shows "p_sorted_1' t a i_1 i"
  sorry
end
