theory stack_top_Why3_ide_VCstack_top_post_top_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_top_lib.Compound_Compound" "frama_c_standard_algorithms_stack_top_lib.Axiomatic_Axiomatic" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (2 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (0 :: int); a_3 :: addr = t_2 a_2; x_1 :: int = x - (1 :: int); x_2 :: int = t_1 (shift a_3 x_1) in (0 :: int) < x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> \<not>p_empty t_1 a \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t (shift a_3 (to_uint32 x_1)) (1 :: int) \<longrightarrow> x_2 = l_top t_2 t_1 a"
  sorry
end
