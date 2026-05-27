theory is_heap_Why3_ide_VCis_heap_assert_rte_mem_access_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_is_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_heap_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal7:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = l_heapparent i_1 in i_1 < i \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> x < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (1 :: int) + i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 x \<longrightarrow> p_isheap t_1 a i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a x) (1 :: int)"
  sorry
end
