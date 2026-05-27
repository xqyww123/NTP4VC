theory axiom_push_of_pop_top_Why3_ide_VCaxiom_push_of_pop_top_post_equal_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_axiom_push_of_pop_top_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_axiom_push_of_pop_top_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); m :: addr \<Rightarrow> int = t_1(a_1 := i); x :: int = l_capacity m a; x_1 :: int = l_size m a; x_2 :: int = (1 :: int) + x_1; m_1 :: addr \<Rightarrow> int = m(a_1 := i_2, shift (t_2 (shift a (0 :: int))) i := i_1); x_3 :: int = l_top t_2 m_1 a; a_2 :: addr = l_storage t_2 a in x = l_capacity t_1 a \<longrightarrow> x_2 = l_size t_1 a \<longrightarrow> l_capacity m_1 a = x \<longrightarrow> x_2 = l_size m_1 a \<longrightarrow> x_3 = l_top t_2 t_1 a \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> \<not>p_empty t_1 a \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 (t_1 a_1) \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> \<not>p_full m a \<longrightarrow> p_invariant t t_2 m a \<longrightarrow> p_unchanged_1' m t_1 a_2 (0 :: int) x_1 \<longrightarrow> \<not>p_empty m_1 a \<longrightarrow> p_unchanged_1' m_1 m a_2 (0 :: int) x_1 \<longrightarrow> p_invariant t t_2 m_1 a \<longrightarrow> is_sint32 x_3 \<longrightarrow> p_equal t_2 m_1 t_2 t_1 a a"
  sorry
end
