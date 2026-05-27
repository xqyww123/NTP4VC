theory sort_heap_Why3_ide_VCsort_heap_loop_inv_reorder_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_sort_heap_lib.Compound_Compound" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_sort_heap_lib.A_Count_A_Count"
begin
theorem goal7:
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int) in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> p_isheap t_1 a i \<longrightarrow> is_sint32 (t_1 a_1) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> p_multisetunchanged_1' t_1 t_1 a (0 :: int) i"
  sorry
end
