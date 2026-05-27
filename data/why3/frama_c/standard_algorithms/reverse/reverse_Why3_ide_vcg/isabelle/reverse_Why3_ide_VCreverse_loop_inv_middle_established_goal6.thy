theory reverse_Why3_ide_VCreverse_loop_inv_middle_established_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_reverse_lib.Compound_Compound" "frama_c_standard_algorithms_reverse_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_uint32 i"
  assumes fact3: "is_uint32 (i cdiv (2 :: int))"
  assumes fact4: "valid_rw t (shift a (0 :: int)) i"
  shows "p_unchanged_1' t_1 t_1 a (0 :: int) i"
  sorry
end
