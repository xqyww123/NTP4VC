theory stack_equal_Why3_ide_VCstack_equal_call_equal_pre_valid_2_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_stack_equal_lib.Compound_Compound" "frama_c_standard_algorithms_stack_equal_lib.Axiomatic_Axiomatic"
begin
theorem goal7:
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (2 :: int); x :: int = t_1 a_2; a_3 :: addr = shift a (2 :: int); x_1 :: int = t_1 a_3; a_4 :: addr = shift a (0 :: int) in x = x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_invariant t t_2 t_1 a_1 \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t (shift (t_2 a_4) (0 :: int)) x"
  sorry
end
