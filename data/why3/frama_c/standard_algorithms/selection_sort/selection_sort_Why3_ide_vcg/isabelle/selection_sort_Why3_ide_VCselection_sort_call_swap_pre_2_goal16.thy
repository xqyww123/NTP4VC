theory selection_sort_Why3_ide_VCselection_sort_call_swap_pre_2_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_selection_sort_lib.Compound_Compound" "frama_c_standard_algorithms_selection_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_selection_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_selection_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal16:
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x_1 :: int = i - i_2; a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_2; x_2 :: int = i_1 - i_2; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i_1; a_4 :: int = a_3 (shift a i); a_5 :: int = a_3 (shift a (i_2 - (1 :: int))) in (0 :: int) \<le> i \<longrightarrow> i < i_1 \<longrightarrow> i_2 \<le> i \<longrightarrow> i \<le> i_1 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> (4294967295 :: int) \<longrightarrow> i_1 \<le> (4294967295 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 x_1 \<longrightarrow> is_sint32 (t_2 (shift a (-(1 :: int)))) \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rd t a_2 x_2 \<longrightarrow> is_sint32 a_4 \<longrightarrow> is_sint32 a_5 \<longrightarrow> p_sorted_1' a_3 a (0 :: int) i_2 \<longrightarrow> p_multisetunchanged_1' a_3 t_2 a (0 :: int) i_1 \<longrightarrow> p_minelement a_3 a_2 x_2 x_1 \<longrightarrow> p_strictlowerbound_1' a_3 a_2 (0 :: int) x_1 a_4 \<longrightarrow> ((0 :: int) < i_2 \<longrightarrow> p_lowerbound_1' a_3 a i_2 i_1 a_5) \<longrightarrow> valid_rw t a_2 (1 :: int)"
  sorry
end
