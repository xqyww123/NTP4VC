theory partial_sort_Why3_ide_VCpartial_sort_assert_rte_unsigned_overflow_goal13
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count"
begin
theorem goal13:
  fixes a :: "addr"
  fixes t_6 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes t_7 :: "addr \<Rightarrow> int"
  fixes t_8 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); x :: int = t_6 a_1; a_2 :: addr = shift a i_3; x_1 :: int = t_7 a_2; x_2 :: int = t_8 a_1; x_3 :: int = i_2 - (1 :: int); a_3 :: addr = shift a x_3; x_4 :: int = t_7 a_3; a_4 :: addr \<Rightarrow> int = havoc t_1 t_5 a_1 i_2; a_5 :: addr \<Rightarrow> int = havoc t_2 a_4 a_1 i_1; a_6 :: int = a_5 a_1; a_7 :: int = a_5 a_2; m :: addr \<Rightarrow> int = t_7(a_3 := x_1, a_2 := i); x_5 :: int = (1 :: int) + i_3 in (0 :: int) < i_2 \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 x_2 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rw t a_1 i_1 \<longrightarrow> valid_rw t a_1 i_2 \<longrightarrow> is_sint32 x_4 \<longrightarrow> is_sint32 (a_4 a_1) \<longrightarrow> p_isheap a_4 a i_2 \<longrightarrow> p_multisetunchanged_1' a_4 t_5 a (0 :: int) i_2 \<longrightarrow> is_sint32 a_6 \<longrightarrow> is_sint32 a_7 \<longrightarrow> p_isheap a_5 a i_2 \<longrightarrow> p_multisetunchanged_1' a_5 t_5 a (0 :: int) i_3 \<longrightarrow> p_unchanged_1' a_5 t_5 a i_3 i_1 \<longrightarrow> p_upperbound_1' a_5 a (0 :: int) i_2 a_6 \<longrightarrow> p_lowerbound_1' a_5 a i_2 i_3 a_6 \<longrightarrow> a_6 \<le> a_7 \<or> x_4 = x \<and> havoc t_3 t_6 a_1 i_2 = t_7 \<and> m a_2 = x_4 \<and> havoc t_4 m a_1 i_2 = t_8 \<and> a_5 = t_6 \<and> p_isheap t_8 a i_2 \<and> p_multisetunchanged_1' t_7 t_6 a (0 :: int) i_2 \<and> valid_rw t a_2 (1 :: int) \<and> p_isheap t_7 a x_3 \<and> p_multisetunchanged_1' t_7 t_5 a (0 :: int) x_5 \<and> p_maxelement t_7 a i_2 x_3 \<and> valid_rw t a_3 (1 :: int) \<and> p_lowerbound_1' t_8 a i_2 x_5 x_2 \<and> p_isheap m a x_3 \<and> p_multisetunchanged_1' t_8 m a (0 :: int) i_2 \<and> p_multisetunchanged_1' t_8 m a (0 :: int) x_5 \<and> p_multisetunchanged_1' m t_7 a (0 :: int) x_5 \<and> p_unchanged_1' m t_7 a x_5 i_1 \<and> p_swappedinside m t_7 a x_3 i_3 x_5 \<longrightarrow> i_3 \<le> (4294967294 :: int)"
  sorry
end
