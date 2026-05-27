theory partial_sort_Why3_ide_VCpartial_sort_assign_exit_part5_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count"
begin
theorem goal15:
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_4 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes t_3 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes t_5 :: "addr \<Rightarrow> int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr \<Rightarrow> int = havoc t_1 t_4 a_1 i_3; a_3 :: addr \<Rightarrow> int = havoc t_2 a_2 a_1 i_2; a_4 :: addr \<Rightarrow> int = havoc t_3 a_3 a_1 i_3; x :: int = i_3 - (1 :: int); a_5 :: addr = shift a x; a_6 :: int = a_4 a_5; a_7 :: int = a_3 a_1; a_8 :: addr = shift a i_4; a_9 :: int = a_3 a_8; x_1 :: int = t_5 a_8; x_2 :: int = t_5 a_5 in a_6 = a_7 \<longrightarrow> (0 :: int) < i_3 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> i_4 \<le> i_2 \<longrightarrow> (0 :: int) \<le> i_3 \<longrightarrow> i_4 < i_2 \<longrightarrow> i_3 \<le> i_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> a_9 < a_7 \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_8 (1 :: int) \<longrightarrow> valid_rw t a_1 i_2 \<longrightarrow> valid_rw t a_1 i_3 \<longrightarrow> is_sint32 x_2 \<longrightarrow> is_sint32 (a_2 a_1) \<longrightarrow> p_isheap a_2 a i_3 \<longrightarrow> p_multisetunchanged_1' a_2 t_4 a (0 :: int) i_3 \<longrightarrow> is_sint32 a_7 \<longrightarrow> is_sint32 a_9 \<longrightarrow> p_isheap a_3 a i_3 \<longrightarrow> p_multisetunchanged_1' a_3 t_4 a (0 :: int) i_4 \<longrightarrow> p_unchanged_1' a_3 t_4 a i_4 i_2 \<longrightarrow> p_upperbound_1' a_3 a (0 :: int) i_3 a_7 \<longrightarrow> p_lowerbound_1' a_3 a i_3 i_4 a_7 \<longrightarrow> is_sint32 a_6 \<longrightarrow> p_isheap a_4 a x \<longrightarrow> p_multisetunchanged_1' a_4 t_4 a (0 :: int) ((1 :: int) + i_4) \<longrightarrow> p_multisetunchanged_1' a_4 a_3 a (0 :: int) i_3 \<longrightarrow> p_maxelement a_4 a i_3 x \<longrightarrow> valid_rw t a_8 (1 :: int) \<and> valid_rw t a_5 (1 :: int) \<or> (t_5(a_5 := x_1, a_8 := i)) a_8 = x_2 \<and> a_4 = t_5 \<and> valid_rw t a_8 (1 :: int) \<and> valid_rw t a_5 (1 :: int) \<longrightarrow> (\<not>invalid t a_8 (1 :: int) \<longrightarrow> included a_8 (1 :: int) a_1 i_2) \<and> (\<not>invalid t a_5 (1 :: int) \<longrightarrow> included a_5 (1 :: int) a_1 i_2)"
  sorry
end
