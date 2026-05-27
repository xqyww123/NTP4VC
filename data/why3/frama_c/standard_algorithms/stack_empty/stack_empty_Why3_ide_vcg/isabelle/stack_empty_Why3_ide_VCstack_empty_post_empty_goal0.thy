theory stack_empty_Why3_ide_VCstack_empty_post_empty_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_stack_empty_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_empty_lib.Compound_Compound"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_size t_1 a in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> p_empty t_1 a \<longleftrightarrow> x = (0 :: int)"
  sorry
end
