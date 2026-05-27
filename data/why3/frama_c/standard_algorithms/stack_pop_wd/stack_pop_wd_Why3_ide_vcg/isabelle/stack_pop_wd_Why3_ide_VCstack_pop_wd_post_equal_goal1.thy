theory stack_pop_wd_Why3_ide_VCstack_pop_wd_post_equal_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_pop_wd_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_pop_wd_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let m :: addr \<Rightarrow> int = t_1(shift a_1 (2 :: int) := i); m_1 :: addr \<Rightarrow> int = m(shift a (2 :: int) := i_1); x :: int = l_capacity m a_1; x_1 :: int = l_capacity t_1 a_1; x_2 :: int = l_size m a_1; x_3 :: int = l_size t_1 a_1; x_4 :: int = l_capacity m_1 a; x_5 :: int = l_capacity m a; x_6 :: int = l_size m_1 a; x_7 :: int = l_size m a; a_2 :: addr = l_storage t_2 a_1; a_3 :: addr = l_storage t_2 a in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_invariant t t_2 t_1 a_1 \<longrightarrow> p_separated t_2 t_1 a_1 a \<longrightarrow> p_equal t_2 t_1 t_2 t_1 a_1 a \<longrightarrow> p_invariant t t_2 m a \<longrightarrow> p_invariant t t_2 m a_1 \<longrightarrow> p_invariant t t_2 m_1 a \<longrightarrow> (p_full m a_1 \<longrightarrow> p_empty t_1 a_1) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> p_empty m a_1) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> x = x_1) \<longrightarrow> (\<not>p_empty t_1 a_1 \<longrightarrow> x = x_1) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> x_2 = x_3) \<longrightarrow> (p_full m_1 a \<longrightarrow> p_empty m a) \<longrightarrow> (p_empty m a \<longrightarrow> p_empty m_1 a) \<longrightarrow> (p_empty m a \<longrightarrow> x_4 = x_5) \<longrightarrow> (\<not>p_empty m a \<longrightarrow> x_4 = x_5) \<longrightarrow> (p_empty m a \<longrightarrow> x_6 = x_7) \<longrightarrow> (\<not>p_empty t_1 a_1 \<longrightarrow> (1 :: int) + x_2 = x_3) \<longrightarrow> (\<not>p_empty m a \<longrightarrow> (1 :: int) + x_6 = x_7) \<longrightarrow> (p_empty t_1 a_1 \<longrightarrow> p_unchanged_1' m t_1 a_2 (0 :: int) x_2) \<longrightarrow> (\<not>p_empty t_1 a_1 \<longrightarrow> p_unchanged_1' m t_1 a_2 (0 :: int) x_2) \<longrightarrow> (p_empty m a \<longrightarrow> p_unchanged_1' m_1 m a_3 (0 :: int) x_6) \<longrightarrow> (\<not>p_empty m a \<longrightarrow> p_unchanged_1' m_1 m a_3 (0 :: int) x_6) \<longrightarrow> p_equal t_2 m_1 t_2 m_1 a_1 a"
  sorry
end
