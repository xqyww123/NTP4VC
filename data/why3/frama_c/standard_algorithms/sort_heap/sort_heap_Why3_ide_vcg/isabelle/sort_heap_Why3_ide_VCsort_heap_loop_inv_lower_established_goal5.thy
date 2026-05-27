theory sort_heap_Why3_ide_VCsort_heap_loop_inv_lower_established_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_sort_heap_lib.Compound_Compound" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_sort_heap_lib.A_Count_A_Count"
begin
theorem goal5:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = t_1 a_1 in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> p_isheap t_1 a i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rw t a_1 i \<longrightarrow> p_lowerbound_1' t_1 a i i x"
  sorry
end
