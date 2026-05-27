theory reverse_Why3_ide_VCreverse_post_reverse_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_reverse_lib.Compound_Compound" "frama_c_standard_algorithms_reverse_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i cdiv (2 :: int); a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i; x_1 :: int = i - i_1 in (0 :: int) \<le> i_1 \<longrightarrow> x \<le> i_1 \<longrightarrow> i_1 \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 + x \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rw t a_1 i \<longrightarrow> p_unchanged_1' a_2 t_2 a i_1 x_1 \<longrightarrow> p_reverse_4' a_2 t_2 a (0 :: int) i_1 x_1 \<longrightarrow> p_reverse_4' a_2 t_2 a x_1 i (0 :: int) \<longrightarrow> p_reverse_5' a_2 t_2 a (0 :: int) i"
  sorry
end
