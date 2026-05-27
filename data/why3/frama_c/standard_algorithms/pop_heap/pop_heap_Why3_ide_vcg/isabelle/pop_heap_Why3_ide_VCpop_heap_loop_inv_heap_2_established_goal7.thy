theory pop_heap_Why3_ide_VCpop_heap_loop_inv_heap_2_established_goal7
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_pop_heap_lib.Compound_Compound" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_pop_heap_lib.A_Count_A_Count"
begin
theorem goal7:
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x_1 :: int = i - (1 :: int); x_2 :: int = t_1 (shift a x_1); a_1 :: addr = shift a (0 :: int); x_3 :: int = t_1 a_1; x_4 :: int = t_1 (shift a (l_heapparent (0 :: int))) in (0 :: int) < i \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_2 < x_3 \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_isheap t_1 a i \<longrightarrow> is_sint32 x_3 \<longrightarrow> p_heapmaximumchild t_1 a i (0 :: int) i_1 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rw t a_1 i \<longrightarrow> is_sint32 x_4 \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t (shift a (to_uint32 x_1)) (1 :: int) \<longrightarrow> ((2 :: int) + i_1 \<le> i \<longrightarrow> l_heapparent i_1 = (0 :: int)) \<longrightarrow> x_2 < x_4"
  sorry
end
