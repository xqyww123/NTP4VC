theory axiom_push_of_pop_top_Why3_ide_VCaxiom_push_of_pop_top_assign_exit_part4_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_axiom_push_of_pop_top_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_axiom_push_of_pop_top_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal1:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); m :: addr \<Rightarrow> int = t_1(a_1 := i); x :: int = l_size m a; x_1 :: int = t_1 a_1; a_2 :: addr = shift (t_2 (shift a (0 :: int))) i in l_capacity m a = l_capacity t_1 a \<longrightarrow> (1 :: int) + x = l_size t_1 a \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> \<not>p_empty t_1 a \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> is_sint32 (l_top t_2 t_1 a) \<longrightarrow> \<not>p_full m a \<longrightarrow> p_invariant t t_2 m a \<longrightarrow> \<not>invalid t a_2 (1 :: int) \<longrightarrow> p_unchanged_1' m t_1 (l_storage t_2 a) (0 :: int) x \<longrightarrow> x_1 = (1 :: int) + i \<or> a_2 = a_1"
  sorry
end
