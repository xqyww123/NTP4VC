theory selection_sort_Why3_ide_VCselection_sort_assert_rte_unsigned_overflow_3_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_selection_sort_lib.Compound_Compound" "frama_c_standard_algorithms_selection_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_selection_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_selection_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal9:
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 + i_2; a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_2; x_1 :: int = i - i_2; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i; a_4 :: int = a_3 (shift a (i_2 - (1 :: int))); a_5 :: int = a_3 (shift a x) in i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> x \<le> i \<longrightarrow> x < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> (4294967295 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 (t_2 (shift a (-(1 :: int)))) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> valid_rd t a_2 x_1 \<longrightarrow> is_sint32 a_4 \<longrightarrow> is_sint32 a_5 \<longrightarrow> p_sorted_1' a_3 a (0 :: int) i_2 \<longrightarrow> p_multisetunchanged_1' a_3 t_2 a (0 :: int) i \<longrightarrow> p_minelement a_3 a_2 x_1 i_1 \<longrightarrow> p_strictlowerbound_1' a_3 a_2 (0 :: int) i_1 a_5 \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> p_lowerbound_1' a_3 a i_2 i a_4) \<longrightarrow> (0 :: int) \<le> x"
  sorry
end
