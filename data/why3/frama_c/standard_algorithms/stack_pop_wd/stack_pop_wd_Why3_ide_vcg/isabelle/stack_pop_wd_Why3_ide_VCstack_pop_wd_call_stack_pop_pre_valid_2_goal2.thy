theory stack_pop_wd_Why3_ide_VCstack_pop_wd_call_stack_pop_pre_valid_2_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_pop_wd_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_pop_wd_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal2:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let m :: addr \<Rightarrow> int = t_1(shift a_1 (2 :: int) := i); x :: int = l_capacity m a_1; x_1 :: int = l_capacity t_1 a_1; x_2 :: int = l_size m a_1; x_3 :: int = l_size t_1 a_1; a_2 :: addr = l_storage t_2 a_1 in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_invariant t t_2 t_1 a_1 \<longrightarrow> p_separated t_2 t_1 a_1 a \<longrightarrow> p_equal t_2 t_1 t_2 t_1 a_1 a \<longrightarrow> p_invariant t t_2 m a_1 \<longrightarrow> (p_full m a_1 \<longrightarrow> p_empty t_1 a_1) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> p_empty m a_1) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> x = x_1) \<longrightarrow> (\<not>p_empty t_1 a_1 \<longrightarrow> x = x_1) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> x_2 = x_3) \<longrightarrow> (\<not>p_empty t_1 a_1 \<longrightarrow> (1 :: int) + x_2 = x_3) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> p_unchanged_1' m t_1 a_2 (0 :: int) x_2) \<longrightarrow> (\<not>p_empty t_1 a_1 \<longrightarrow> p_unchanged_1' m t_1 a_2 (0 :: int) x_2) \<longrightarrow> p_invariant t t_2 m a"
  sorry
end
