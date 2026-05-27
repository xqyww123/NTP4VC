theory pop_heap_Why3_ide_VCpop_heap_assert_rte_mem_access_2_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_pop_heap_lib.Compound_Compound"
begin
theorem goal5:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = i - (1 :: int) in (0 :: int) < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> p_isheap t_1 a i \<longrightarrow> is_sint32 (t_1 a_1) \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> is_sint32 (t_1 (shift a x)) \<longrightarrow> valid_rd t (shift a (to_uint32 x)) (1 :: int)"
  sorry
end
