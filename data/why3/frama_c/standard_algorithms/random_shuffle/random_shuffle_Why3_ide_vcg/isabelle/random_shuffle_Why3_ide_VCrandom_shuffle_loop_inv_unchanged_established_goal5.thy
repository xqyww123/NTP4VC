theory random_shuffle_Why3_ide_VCrandom_shuffle_loop_inv_unchanged_established_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_random_shuffle_lib.Compound_Compound" "frama_c_standard_algorithms_random_shuffle_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "(0 :: int) < i"
  assumes fact1: "region (base a) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "is_uint32 i"
  assumes fact4: "valid_rw t (shift a (0 :: int)) i"
  shows "p_unchanged_1' t_1 t_1 a (1 :: int) i"
  sorry
end
