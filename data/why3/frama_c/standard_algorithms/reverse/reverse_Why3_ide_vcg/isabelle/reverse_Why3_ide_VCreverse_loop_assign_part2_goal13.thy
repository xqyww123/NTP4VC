theory reverse_Why3_ide_VCreverse_loop_assign_part2_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_reverse_lib.Compound_Compound" "frama_c_standard_algorithms_reverse_lib.Axiomatic_Axiomatic"
begin
theorem goal13:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_1; a_3 :: addr = shift a (i_1 - (1 :: int) - i_2); a_4 :: addr = shift a i_2; a_5 :: int = a_2 a_3; a_6 :: int = (a_2(a_4 := a_5, a_3 := i)) a_3; a_7 :: int = a_2 a_4; x_1 :: int = i_1 cdiv (2 :: int); x_2 :: int = to_uint32 (i_1 - (1 :: int)); x_3 :: int = i_1 - i_2 in a_6 = a_7 \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < x_1 \<longrightarrow> i_2 \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 + x_1 \<le> i_1 \<longrightarrow> i_2 \<le> x_2 \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> x_2 \<le> (4294967295 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 x_1 \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rw t a_4 (1 :: int) \<longrightarrow> is_sint32 a_7 \<longrightarrow> is_sint32 a_5 \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> is_sint32 a_6 \<longrightarrow> p_unchanged_1' a_2 t_2 a i_2 x_3 \<longrightarrow> p_reverse_4' a_2 t_2 a (0 :: int) i_2 x_3 \<longrightarrow> p_reverse_4' a_2 t_2 a x_3 i_1 (0 :: int) \<longrightarrow> (\<not>invalid t a_4 (1 :: int) \<longrightarrow> included a_4 (1 :: int) a_1 i_1) \<and> (\<not>invalid t a_3 (1 :: int) \<longrightarrow> included a_3 (1 :: int) a_1 i_1)"
  sorry
end
