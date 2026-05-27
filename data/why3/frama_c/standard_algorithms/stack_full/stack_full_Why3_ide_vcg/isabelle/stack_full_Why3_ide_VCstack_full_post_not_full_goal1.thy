theory stack_full_Why3_ide_VCstack_full_post_not_full_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_stack_full_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_full_lib.Compound_Compound"
begin
theorem goal1:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_size t_1 a; a_1 :: addr = shift a (1 :: int); x_1 :: int = t_1 a_1 in region (base a) \<le> (0 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> \<not>p_full t_1 a \<longleftrightarrow> \<not>x_1 = x"
  sorry
end
