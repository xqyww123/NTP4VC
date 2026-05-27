theory stack_push_Why3_ide_VCstack_push_not_full_post_top_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_stack_push_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_stack_push_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal8:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_1 :: addr = shift a (2 :: int); x :: int = t_1 a_1; a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift (t_2 a_2) x in region (base a) \<le> (0 :: int) \<longrightarrow> x \<le> (4294967294 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_sint32 i \<longrightarrow> \<not>p_full t_1 a \<longrightarrow> valid_rw t a (3 :: int) \<longrightarrow> is_uint32 x \<longrightarrow> p_invariant t t_2 t_1 a \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_1 (1 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> l_top t_2 (t_1(a_3 := i, a_1 := (1 :: int) + x)) a = i"
  sorry
end
