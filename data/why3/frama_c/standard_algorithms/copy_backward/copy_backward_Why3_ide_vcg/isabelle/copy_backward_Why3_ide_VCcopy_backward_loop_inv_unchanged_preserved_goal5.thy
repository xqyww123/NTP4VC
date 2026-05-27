theory copy_backward_Why3_ide_VCcopy_backward_loop_inv_unchanged_preserved_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_copy_backward_lib.Compound_Compound" "frama_c_standard_algorithms_copy_backward_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 - (1 :: int); a_2 :: addr = shift a_1 (0 :: int); a_3 :: addr = shift a (0 :: int); a_4 :: addr = shift a_1 x; a_5 :: addr = shift a x; a_6 :: addr \<Rightarrow> int = havoc t_1 t_2 a_3 i in (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rd t a_2 i \<longrightarrow> valid_rw t a_3 i \<longrightarrow> separated a_2 i (shift a i) (1 :: int) \<longrightarrow> valid_rd t a_4 (1 :: int) \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> p_unchanged_1' a_6 t_2 a_1 (0 :: int) i_1 \<longrightarrow> p_equalranges_2' a_6 t_2 a_1 i_1 i a \<longrightarrow> p_unchanged_1' (a_6(a_5 := a_6 a_4)) t_2 a_1 (0 :: int) x"
  sorry
end
