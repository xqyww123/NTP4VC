theory stack_push_Why3_ide_VCstack_push_assert_rte_mem_access_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_push_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_push_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> \<not>p_full t_1 a \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 (t_1 a_1) \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
