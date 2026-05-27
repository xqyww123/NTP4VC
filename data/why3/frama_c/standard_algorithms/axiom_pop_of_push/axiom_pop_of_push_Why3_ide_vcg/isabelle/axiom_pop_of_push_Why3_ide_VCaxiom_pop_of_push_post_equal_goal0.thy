theory axiom_pop_of_push_Why3_ide_VCaxiom_pop_of_push_post_equal_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_axiom_pop_of_push_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_axiom_pop_of_push_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); x :: int = t_1 a_1; m :: addr \<Rightarrow> int = t_1(shift (t_2 (shift a (0 :: int))) x := i); m_1 :: addr \<Rightarrow> int = m(a_1 := i_1); x_1 :: int = l_capacity m_1 a; m_2 :: addr \<Rightarrow> int = m(a_1 := i_2); x_2 :: int = l_size m_2 a; x_3 :: int = l_size t_1 a; a_2 :: addr = l_storage t_2 a in x_1 = l_capacity t_1 a \<longrightarrow> l_capacity m_2 a = x_1 \<longrightarrow> x_2 = x_3 \<longrightarrow> (1 :: int) + x_3 = l_size m_1 a \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> \<not>p_full t_1 a \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> \<not>p_empty m_1 a \<longrightarrow> \<not>p_full m_2 a \<longrightarrow> p_unchanged_1' m_1 t_1 a_2 (0 :: int) x_3 \<longrightarrow> p_invariant t t_2 m_1 a \<longrightarrow> p_invariant t t_2 m_2 a \<longrightarrow> is_sint32 (l_top t_2 m_1 a) \<longrightarrow> p_unchanged_1' m_2 m_1 a_2 (0 :: int) x_2 \<longrightarrow> p_equal t_2 m_2 t_2 t_1 a a"
  sorry
end
