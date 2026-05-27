theory stack_push_Why3_ide_VCstack_push_full_post_unchanged_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_push_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_push_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal5:
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "framed t_2"
  assumes fact2: "linked t"
  assumes fact3: "p_full t_1 a"
  assumes fact4: "valid_rw t a (3 :: int)"
  assumes fact5: "p_invariant t t_2 t_1 a"
  shows "p_unchanged_1' t_1 t_1 (l_storage t_2 a) (0 :: int) (l_size t_1 a)"
  sorry
end
