theory stack_top_Why3_ide_VCstack_top_assert_rte_mem_access_2_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_top_lib.Compound_Compound" "frama_c_standard_algorithms_stack_top_lib.Axiomatic_Axiomatic" "Why3STD.Cint_Cint"
begin
theorem goal2:
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
  shows "valid_rd t (shift (t_2 (shift a (0 :: int))) (0 :: int)) (1 :: int)"
  sorry
end
