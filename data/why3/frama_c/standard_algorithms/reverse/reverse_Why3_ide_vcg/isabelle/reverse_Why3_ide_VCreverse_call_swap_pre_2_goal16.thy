theory reverse_Why3_ide_VCreverse_call_swap_pre_2_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_reverse_lib.Compound_Compound" "frama_c_standard_algorithms_reverse_lib.Axiomatic_Axiomatic"
begin
theorem goal16:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i cdiv (2 :: int); x_1 :: int = to_uint32 (i - (1 :: int)); a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i; x_3 :: int = i - i_1 in (0 :: int) < i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < x \<longrightarrow> i_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 + x \<le> i \<longrightarrow> i_1 \<le> x_1 \<longrightarrow> x_1 \<le> (4294967295 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rw t a_1 i \<longrightarrow> p_unchanged_1' a_2 t_2 a i_1 x_3 \<longrightarrow> p_reverse_4' a_2 t_2 a (0 :: int) i_1 x_3 \<longrightarrow> p_reverse_4' a_2 t_2 a x_3 i (0 :: int) \<longrightarrow> valid_rw t (shift a (i - (1 :: int) - i_1)) (1 :: int)"
  sorry
end
