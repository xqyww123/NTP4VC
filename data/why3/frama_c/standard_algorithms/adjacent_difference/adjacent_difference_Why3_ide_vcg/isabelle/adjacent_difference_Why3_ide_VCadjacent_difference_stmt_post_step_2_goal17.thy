theory adjacent_difference_Why3_ide_VCadjacent_difference_stmt_post_step_2_goal17
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_adjacent_difference_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic_Axiomatic"
begin
theorem goal17:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 (t_2(a_2 := t_2 a_3)) (shift a (1 :: int)) (i - (1 :: int)); a_5 :: addr = shift a_1 i_1; a_6 :: int = a_4 a_5; x :: int = i_1 - (1 :: int); a_7 :: addr = shift a_1 (to_uint32 x); a_8 :: int = a_4 a_7; a_9 :: addr = shift a i_1; a_10 :: int = a_4 (shift a_1 x); a_11 :: int = a_6 - a_10 in (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> a_6 \<le> (2147483647 :: int) + a_8 \<longrightarrow> a_8 \<le> (2147483648 :: int) + a_6 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_adjacentdifferencebounds t_2 a_1 i \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_3 i \<longrightarrow> valid_rd t a_5 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_9 (1 :: int) \<longrightarrow> separated a_3 i a_2 i \<longrightarrow> valid_rd t a_7 (1 :: int) \<longrightarrow> is_sint32 a_6 \<longrightarrow> is_sint32 a_10 \<longrightarrow> is_sint32 a_8 \<longrightarrow> p_unchanged_1' a_4 t_2 a_1 (0 :: int) i \<longrightarrow> p_adjacentdifference a_4 a_1 i_1 a \<longrightarrow> is_sint32 a_11 \<longrightarrow> a_6 = a_10 + l_difference (a_4(a_9 := a_11)) a_1 i_1"
  sorry
end
