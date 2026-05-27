theory axiom_size_of_init_Why3_ide_VCaxiom_size_of_init_post_size_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_axiom_size_of_init_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_axiom_size_of_init_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let m :: addr \<Rightarrow> int = t_1(shift a_1 (1 :: int) := i_1, shift a_1 (2 :: int) := i); x :: int = l_capacity m a_1; m_1 :: addr \<Rightarrow> addr = t_2(shift a_1 (0 :: int) := a); a_2 :: addr = l_storage m_1 a_1; x_1 :: int = l_size m a_1; a_3 :: addr = shift a_2 (0 :: int) in region (base a_1) \<le> (0 :: int) \<longrightarrow> (0 :: int) < x \<longrightarrow> region (base a_2) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> p_empty m a_1 \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_invariant t m_1 m a_1 \<longrightarrow> valid_rw t a_3 x \<longrightarrow> separated a_1 (3 :: int) a_3 x \<longrightarrow> x_1 = (0 :: int)"
  sorry
end
