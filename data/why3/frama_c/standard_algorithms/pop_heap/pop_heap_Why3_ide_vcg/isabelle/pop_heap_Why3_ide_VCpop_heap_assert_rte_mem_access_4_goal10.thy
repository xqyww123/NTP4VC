theory pop_heap_Why3_ide_VCpop_heap_assert_rte_mem_access_4_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_pop_heap_lib.Compound_Compound" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_pop_heap_lib.A_Count_A_Count"
begin
theorem goal10:
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_heapparent i_2; x_1 :: int = i - (1 :: int); a_1 :: addr = shift a x_1; x_2 :: int = t_2 a_1; a_2 :: addr = shift a (0 :: int); x_3 :: int = t_2 a_2; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 x_1; a_4 :: int = a_3 a_1; a_5 :: int = a_3 (shift a (l_heapparent x)) in (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> x < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_2 < x_3 \<longrightarrow> a_4 < a_5 \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> (2 :: int) + i_2 \<le> i \<longrightarrow> (2 :: int) + x \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 x \<longrightarrow> p_isheap t_2 a i \<longrightarrow> is_sint32 x_3 \<longrightarrow> p_heapmaximumchild t_2 a i (0 :: int) i_1 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rw t a_2 i \<longrightarrow> is_sint32 (t_2 (shift a (l_heapparent (0 :: int)))) \<longrightarrow> is_sint32 x_2 \<longrightarrow> is_sint32 a_4 \<longrightarrow> is_sint32 a_5 \<longrightarrow> valid_rd t (shift a (to_uint32 x_1)) (1 :: int) \<longrightarrow> p_isheap a_3 a i \<longrightarrow> p_upperbound_1' a_3 a (0 :: int) i x_3 \<longrightarrow> p_heapmaximumchild a_3 a i x i_2 \<longrightarrow> ((2 :: int) + i_1 \<le> i \<longrightarrow> l_heapparent i_1 = (0 :: int)) \<longrightarrow> valid_rd t (shift a i_2) (1 :: int)"
  sorry
end
