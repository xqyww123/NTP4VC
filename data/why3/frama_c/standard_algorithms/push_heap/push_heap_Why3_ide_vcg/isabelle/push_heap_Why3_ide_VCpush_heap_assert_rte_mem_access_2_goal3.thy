theory push_heap_Why3_ide_VCpush_heap_assert_rte_mem_access_2_goal3
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_push_heap_lib.Compound_Compound" "frama_c_standard_algorithms_push_heap_lib.Axiomatic_Axiomatic"
begin
theorem goal3:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = i - (1 :: int); x_1 :: int = l_heapparent x in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> valid_rw t (shift a (0 :: int)) i \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_isheap t_1 a x \<longrightarrow> is_sint32 (t_1 (shift a x)) \<longrightarrow> valid_rd t (shift a (to_uint32 x)) (1 :: int) \<longrightarrow> valid_rd t (shift a x_1) (1 :: int)"
  sorry
end
