theory partial_sort_Why3_ide_VCpartial_sort_assert_rte_mem_access_2_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count"
begin
theorem goal12:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_3 a_1 i_1; a_3 :: addr \<Rightarrow> int = havoc t_2 a_2 a_1 i; a_4 :: int = a_3 a_1 in (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> valid_rw t a_1 i \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> is_sint32 (a_2 a_1) \<longrightarrow> p_isheap a_2 a i_1 \<longrightarrow> p_multisetunchanged_1' a_2 t_3 a (0 :: int) i_1 \<longrightarrow> is_sint32 a_4 \<longrightarrow> p_isheap a_3 a i_1 \<longrightarrow> p_multisetunchanged_1' a_3 t_3 a (0 :: int) i_2 \<longrightarrow> p_unchanged_1' a_3 t_3 a i_2 i \<longrightarrow> p_upperbound_1' a_3 a (0 :: int) i_1 a_4 \<longrightarrow> p_lowerbound_1' a_3 a i_1 i_2 a_4 \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
