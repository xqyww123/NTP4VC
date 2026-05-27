theory stack_init_Why3_ide_VCstack_init_post_storage_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_stack_init_lib.Compound_Compound" "frama_c_standard_algorithms_stack_init_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int) in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> framed t_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_1 (3 :: int) \<longrightarrow> valid_rw t (shift a_1 (1 :: int)) (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t (shift a_1 (2 :: int)) (1 :: int) \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_1 (3 :: int) a_3 i \<longrightarrow> l_storage (t_1(a_2 := a)) a_1 = a"
  sorry
end
