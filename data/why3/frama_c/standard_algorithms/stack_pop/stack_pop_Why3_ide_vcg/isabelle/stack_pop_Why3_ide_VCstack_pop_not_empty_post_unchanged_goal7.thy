theory stack_pop_Why3_ide_VCstack_pop_not_empty_post_unchanged_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_pop_lib.Compound_Compound" "frama_c_standard_algorithms_stack_pop_lib.Axiomatic_Axiomatic" "Why3STD.Cint_Cint"
begin
theorem goal7:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); x :: int = t_1 a_1; m :: addr \<Rightarrow> int = t_1(a_1 := x - (1 :: int)) in (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> \<not>p_empty t_1 a \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> p_unchanged_1' m t_1 (l_storage t_2 a) (0 :: int) (l_size m a)"
  sorry
end
