theory stack_pop_Why3_ide_VCstack_pop_empty_post_unchanged_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_pop_lib.Compound_Compound" "frama_c_standard_algorithms_stack_pop_lib.Axiomatic_Axiomatic" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "framed t_2"
  assumes fact2: "linked t"
  assumes fact3: "p_empty t_1 a"
  assumes fact4: "valid_rw t a (3 :: int)"
  assumes fact5: "p_invariant t t_2 t_1 a"
  shows "p_unchanged_1' t_1 t_1 (l_storage t_2 a) (0 :: int) (l_size t_1 a)"
  sorry
end
