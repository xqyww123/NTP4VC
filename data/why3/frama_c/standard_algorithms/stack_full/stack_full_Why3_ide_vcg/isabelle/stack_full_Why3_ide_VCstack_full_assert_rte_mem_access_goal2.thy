theory stack_full_Why3_ide_VCstack_full_assert_rte_mem_access_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_stack_full_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_full_lib.Compound_Compound"
begin
theorem goal2:
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (1 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 (l_size t_1 a) \<longrightarrow> is_uint32 (t_1 a_1) \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
