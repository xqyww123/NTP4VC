theory pop_heap_Why3_ide_VCpop_heap_assign_normal_part4_goal16
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_pop_heap_lib.Compound_Compound" "frama_c_standard_algorithms_pop_heap_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_pop_heap_lib.A_Count_A_Count"
begin
theorem goal16:
  fixes i :: "int"
  fixes a :: "addr"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let x :: int = i - (1 :: int); a_1 :: addr = shift a x; x_1 :: int = t_2 a_1; a_2 :: addr = shift a (0 :: int); x_2 :: int = t_2 a_2; a_3 :: addr \<Rightarrow> int = havoc t_1 t_2 a_2 x; a_4 :: int = a_3 a_1; a_5 :: int = a_3 (shift a (l_heapparent i_1)); a_6 :: addr = shift a i_1; a_7 :: addr = shift a i_3 in (0 :: int) < i \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_1 < x_2 \<longrightarrow> a_4 < a_5 \<longrightarrow> (2 :: int) \<le> i \<longrightarrow> (2 :: int) + i_1 \<le> i \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> p_isheap t_2 a i \<longrightarrow> is_sint32 x_2 \<longrightarrow> p_heapmaximumchild t_2 a i (0 :: int) i_2 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rw t a_2 i \<longrightarrow> valid_rw t a_6 (1 :: int) \<longrightarrow> \<not>invalid t a_6 (1 :: int) \<longrightarrow> is_sint32 (t_2 (shift a (l_heapparent (0 :: int)))) \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 a_5 \<longrightarrow> is_sint32 a_4 \<longrightarrow> valid_rd t (shift a (to_uint32 x)) (1 :: int) \<longrightarrow> p_isheap a_3 a i \<longrightarrow> p_upperbound_1' a_3 a (0 :: int) i x_2 \<longrightarrow> p_heapmaximumchild a_3 a i i_1 i_3 \<longrightarrow> ((2 :: int) + i_2 \<le> i \<longrightarrow> l_heapparent i_2 = (0 :: int)) \<longrightarrow> ((2 :: int) + i_3 \<le> i \<longrightarrow> l_heapparent i_3 = i_1) \<longrightarrow> i \<le> (1 :: int) + i_3 \<or> a_3 = t_3 \<and> t_3 a_7 \<le> t_3 a_1 \<and> valid_rd t a_7 (1 :: int) \<longrightarrow> included a_6 (1 :: int) a_2 i"
  sorry
end
