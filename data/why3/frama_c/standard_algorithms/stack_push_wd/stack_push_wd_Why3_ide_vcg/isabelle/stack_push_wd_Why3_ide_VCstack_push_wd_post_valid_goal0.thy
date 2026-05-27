theory stack_push_wd_Why3_ide_VCstack_push_wd_post_valid_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_push_wd_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_push_wd_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (2 :: int); x :: int = t_1 a_2; m :: addr \<Rightarrow> int = t_1(a_2 := i_1, shift (t_2 (shift a_1 (0 :: int))) x := i); x_1 :: int = l_size t_1 a_1; a_3 :: addr = shift a (2 :: int); x_2 :: int = m a_3; x_3 :: int = l_top t_2 m a_1; m_1 :: addr \<Rightarrow> int = m(a_3 := i_3, shift (t_2 (shift a (0 :: int))) x_2 := i_2); x_4 :: int = l_capacity m_1 a; x_5 :: int = l_capacity m a; x_6 :: int = l_size m_1 a; x_7 :: int = l_size m a; a_4 :: addr = l_storage t_2 a in l_capacity m a_1 = l_capacity t_1 a_1 \<longrightarrow> (1 :: int) + x_1 = l_size m a_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> \<not>p_full t_1 a \<longrightarrow> \<not>p_full t_1 a_1 \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> is_uint32 (t_1 a_3) \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_invariant t t_2 t_1 a_1 \<longrightarrow> p_separated t_2 t_1 a_1 a \<longrightarrow> p_equal t_2 t_1 t_2 t_1 a_1 a \<longrightarrow> is_uint32 x_2 \<longrightarrow> \<not>p_empty m a_1 \<longrightarrow> p_unchanged_1' m t_1 (l_storage t_2 a_1) (0 :: int) x_1 \<longrightarrow> p_invariant t t_2 m a \<longrightarrow> p_invariant t t_2 m a_1 \<longrightarrow> is_sint32 x_3 \<longrightarrow> (p_empty m_1 a \<longrightarrow> p_full m a) \<longrightarrow> (p_full m a \<longrightarrow> p_full m_1 a) \<longrightarrow> (p_full m a \<longrightarrow> x_4 = x_5) \<longrightarrow> (\<not>p_full m a \<longrightarrow> x_4 = x_5) \<longrightarrow> (p_full m a \<longrightarrow> x_6 = x_7) \<longrightarrow> (\<not>p_full m a \<longrightarrow> (1 :: int) + x_7 = x_6) \<longrightarrow> (\<not>p_full m a \<longrightarrow> l_top t_2 m_1 a = x_3) \<longrightarrow> (\<not>p_full m a \<longrightarrow> p_unchanged_1' m_1 m a_4 (0 :: int) x_7) \<longrightarrow> (p_full m a \<longrightarrow> p_invariant t t_2 m_1 a) \<longrightarrow> (\<not>p_full m a \<longrightarrow> p_invariant t t_2 m_1 a) \<longrightarrow> (p_full m a \<longrightarrow> p_unchanged_1' m_1 m a_4 (0 :: int) x_6) \<longrightarrow> p_invariant t t_2 m_1 a \<and> p_invariant t t_2 m_1 a_1"
  sorry
end
