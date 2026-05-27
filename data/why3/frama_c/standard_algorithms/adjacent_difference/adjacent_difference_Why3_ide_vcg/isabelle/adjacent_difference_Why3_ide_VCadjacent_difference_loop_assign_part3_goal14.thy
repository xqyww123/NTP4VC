theory adjacent_difference_Why3_ide_VCadjacent_difference_loop_assign_part3_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_adjacent_difference_lib.Compound_Compound" "frama_c_standard_algorithms_adjacent_difference_lib.A_DifferenceAxiomatic_A_DifferenceAxiomatic" "frama_c_standard_algorithms_adjacent_difference_lib.Axiomatic_Axiomatic"
begin
theorem goal14:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a_1 (0 :: int); a_4 :: addr = shift a (1 :: int); x :: int = i_1 - (1 :: int); a_5 :: addr \<Rightarrow> int = havoc t_1 (t_2(a_2 := t_2 a_3)) a_4 x; a_6 :: addr = shift a i_2; a_7 :: addr \<Rightarrow> int = a_5(a_6 := i); a_8 :: addr = shift a_1 i_2; a_9 :: int = a_5 a_8; a_10 :: addr = shift a_1 (to_uint32 (i_2 - (1 :: int))); a_11 :: int = a_5 a_10 in l_difference a_7 a_1 i_2 = i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> a_9 \<le> (2147483647 :: int) + a_11 \<longrightarrow> a_11 \<le> (2147483648 :: int) + a_9 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> p_adjacentdifferencebounds t_2 a_1 i_1 \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t a_3 i_1 \<longrightarrow> valid_rd t a_8 (1 :: int) \<longrightarrow> valid_rw t a_2 (1 :: int) \<longrightarrow> valid_rw t a_2 i_1 \<longrightarrow> valid_rw t a_6 (1 :: int) \<longrightarrow> \<not>invalid t a_6 (1 :: int) \<longrightarrow> separated a_3 i_1 a_2 i_1 \<longrightarrow> valid_rd t a_10 (1 :: int) \<longrightarrow> is_sint32 a_9 \<longrightarrow> is_sint32 a_11 \<longrightarrow> p_unchanged_1' a_5 t_2 a_1 (0 :: int) i_1 \<longrightarrow> p_adjacentdifference a_5 a_1 i_2 a \<longrightarrow> p_unchanged_1' a_7 a_5 a (0 :: int) i_2 \<longrightarrow> included a_6 (1 :: int) a_4 x"
  sorry
end
