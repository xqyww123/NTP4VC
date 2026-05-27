theory stack_push_wd_Why3_ide_VCstack_push_wd_call_stack_push_pre_valid_2_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_push_wd_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_push_wd_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (2 :: int); x :: int = t_1 a_2; m :: addr \<Rightarrow> int = t_1(a_2 := i_1, shift (t_2 (shift a_1 (0 :: int))) x := i); x_1 :: int = l_size t_1 a_1; a_3 :: addr = shift a (2 :: int) in l_capacity m a_1 = l_capacity t_1 a_1 \<longrightarrow> (1 :: int) + x_1 = l_size m a_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> \<not>p_full t_1 a \<longrightarrow> \<not>p_full t_1 a_1 \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> is_uint32 (t_1 a_3) \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_invariant t t_2 t_1 a_1 \<longrightarrow> p_separated t_2 t_1 a_1 a \<longrightarrow> p_equal t_2 t_1 t_2 t_1 a_1 a \<longrightarrow> is_uint32 (m a_3) \<longrightarrow> \<not>p_empty m a_1 \<longrightarrow> p_unchanged_1' m t_1 (l_storage t_2 a_1) (0 :: int) x_1 \<longrightarrow> p_invariant t t_2 m a_1 \<longrightarrow> is_sint32 (l_top t_2 m a_1) \<longrightarrow> p_invariant t t_2 m a"
  sorry
end
