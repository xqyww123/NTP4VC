theory adjacent_difference_Why3_ide_VCadjacent_difference_loop_inv_unchanged_preserved_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_adjacent_difference_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr \<Rightarrow> int = havoc t_1 (t_2(a_2 := t_2 a_3)) (shift a (1 :: int)) (i_1 - (1 :: int)); a_5 :: addr = shift a i_2; a_6 :: addr \<Rightarrow> int = a_4(a_5 := i); a_7 :: addr = shift a_1 i_2; a_8 :: int = a_4 a_7; a_9 :: addr = shift a_1 (to_uint32 (i_2 - (1 :: int))); a_10 :: int = a_4 a_9 in l_difference a_6 a_1 i_2 = i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> a_8 \<le> (2147483647 :: int) + a_10 \<longrightarrow> a_10 \<le> (2147483648 :: int) + a_8 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> p_adjacentdifferencebounds t_2 a_1 i_1 \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_3 i_1 \<longrightarrow> valid_rd t a_7 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_5 (1 :: int) \<longrightarrow> separated a_3 i_1 a_2 i_1 \<longrightarrow> valid_rd t a_9 (1 :: int) \<longrightarrow> is_sint32 a_8 \<longrightarrow> is_sint32 a_10 \<longrightarrow> p_unchanged_1' a_4 t_2 a_1 (0 :: int) i_1 \<longrightarrow> p_adjacentdifference a_4 a_1 i_2 a \<longrightarrow> p_unchanged_1' a_6 a_4 a (0 :: int) i_2 \<longrightarrow> p_unchanged_1' a_6 t_2 a_1 (0 :: int) i_1"
  sorry
end
