theory CountSectionUnion_Why3_ide_VCCountSectionUnion_loop_inv_2_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_sort_heap_lib.A_Count_A_Count" "frama_c_standard_algorithms_sort_heap_lib.Compound_Compound" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes t :: "addr \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_3 in i_1 \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_3 < i \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i_4 \<longrightarrow> is_uint32 x \<longrightarrow> (\<forall>(i_5 :: int). is_sint32 i_5 \<longrightarrow> l_count_1' t a i_1 i_3 i_5 + l_count_1' t a i_2 i_1 i_5 = l_count_1' t a i_2 i_3 i_5) \<longrightarrow> l_count_1' t a i_2 i_1 i_4 + l_count_1' t a i_1 x i_4 = l_count_1' t a i_2 x i_4"
  sorry
end
