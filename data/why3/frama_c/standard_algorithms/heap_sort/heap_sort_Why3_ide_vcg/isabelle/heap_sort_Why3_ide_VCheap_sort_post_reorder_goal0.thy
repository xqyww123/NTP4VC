theory heap_sort_Why3_ide_VCheap_sort_post_reorder_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_heap_sort_lib.Compound_Compound" "frama_c_standard_algorithms_heap_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_heap_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_heap_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_2 t_3 a_1 i; a_3 :: addr \<Rightarrow> int = havoc t_1 t_3 a_1 i in region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t a_1 i \<longrightarrow> p_sorted_1' a_2 a (0 :: int) i \<longrightarrow> p_isheap a_3 a i \<longrightarrow> p_multisetunchanged_1' a_3 t_3 a (0 :: int) i \<longrightarrow> p_multisetunchanged_1' a_2 a_3 a (0 :: int) i \<longrightarrow> p_multisetunchanged_1' a_2 t_3 a (0 :: int) i"
  sorry
end
