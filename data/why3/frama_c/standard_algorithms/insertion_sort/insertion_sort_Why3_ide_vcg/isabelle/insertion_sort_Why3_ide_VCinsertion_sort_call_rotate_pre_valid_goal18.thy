theory insertion_sort_Why3_ide_VCinsertion_sort_call_rotate_pre_valid_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_insertion_sort_lib.Compound_Compound" "frama_c_standard_algorithms_insertion_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_insertion_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_insertion_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal18:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_2; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i; a_4 :: int = a_3 a_2 in i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967295 :: int) + i_1 \<longrightarrow> to_uint32 (i_2 - i_1) \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rd t a_1 i_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> is_sint32 a_4 \<longrightarrow> p_sorted_1' a_3 a (0 :: int) i_2 \<longrightarrow> p_unchanged_1' a_3 t_2 a i_2 i \<longrightarrow> p_multisetunchanged_1' a_3 t_2 a (0 :: int) i_2 \<longrightarrow> p_upperbound_1' a_3 a (0 :: int) i_1 a_4 \<longrightarrow> p_strictlowerbound_1' a_3 a i_1 i_2 a_4 \<longrightarrow> valid_rw t (shift a i_1) ((1 :: int) + i_2 - i_1)"
  sorry
end
