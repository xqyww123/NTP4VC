theory reverse_copy_Why3_ide_VCreverse_copy_loop_inv_bound_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_reverse_copy_lib.Compound_Compound" "frama_c_standard_algorithms_reverse_copy_lib.Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes i :: "int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = to_uint32 (i - (1 :: int)); a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int) in (0 :: int) < i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_1 \<le> x \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> x \<le> (4294967295 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 ((1 :: int) + i_1) \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> valid_rw t (shift a i_1) (1 :: int) \<longrightarrow> separated a_2 i a_3 i \<longrightarrow> p_reverse_2' t_2 (havoc t_1 t_2 a_3 i) a (0 :: int) i_1 a_1 (i - i_1) \<longrightarrow> valid_rd t (shift a_1 (to_uint32 (x - i_1))) (1 :: int) \<longrightarrow> -(1 :: int) \<le> i_1"
  sorry
end
