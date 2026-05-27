theory is_sorted_Why3_ide_VCis_sorted_loop_inv_sorted_established_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i"
  shows "p_weaklysorted_1' t_1 a (0 :: int) (1 :: int)"
  sorry
end
