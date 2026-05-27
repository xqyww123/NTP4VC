theory sort_heap_Why3_ide_VCsort_heap_call_pop_heap_pre_valid_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_sort_heap_lib.Compound_Compound" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_sort_heap_lib.A_Count_A_Count"
begin
theorem goal12:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_2 a_1 i; a_3 :: int = a_2 a_1 in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_isheap t_2 a i \<longrightarrow> is_sint32 (t_2 a_1) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> is_sint32 a_3 \<longrightarrow> p_isheap a_2 a i_1 \<longrightarrow> p_sorted_1' a_2 a i_1 i \<longrightarrow> p_multisetunchanged_1' a_2 t_2 a (0 :: int) i \<longrightarrow> p_lowerbound_1' a_2 a i_1 i a_3 \<longrightarrow> valid_rw t a_1 i_1"
  sorry
end
