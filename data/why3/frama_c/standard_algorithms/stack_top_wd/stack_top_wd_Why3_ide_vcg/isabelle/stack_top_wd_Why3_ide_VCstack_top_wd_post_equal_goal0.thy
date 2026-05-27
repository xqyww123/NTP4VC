theory stack_top_wd_Why3_ide_VCstack_top_wd_post_equal_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_top_wd_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_top_wd_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_top t_2 t_1 a; x_1 :: int = l_top t_2 t_1 a_1 in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> \<not>p_empty t_1 a \<longrightarrow> \<not>p_empty t_1 a_1 \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_invariant t t_2 t_1 a_1 \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> p_equal t_2 t_1 t_2 t_1 a_1 a \<longrightarrow> x_1 = x"
  sorry
end
