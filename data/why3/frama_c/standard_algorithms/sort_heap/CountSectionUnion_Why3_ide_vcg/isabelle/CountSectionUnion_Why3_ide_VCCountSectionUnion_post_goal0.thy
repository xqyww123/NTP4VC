theory CountSectionUnion_Why3_ide_VCCountSectionUnion_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_sort_heap_lib.A_Count_A_Count" "frama_c_standard_algorithms_sort_heap_lib.Compound_Compound" "frama_c_standard_algorithms_sort_heap_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes i_3 :: "int"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_2 \<le> i"
  assumes fact1: "i_4 \<le> i"
  assumes fact2: "i_1 \<le> i_2"
  assumes fact3: "i \<le> i_4"
  assumes fact4: "i_2 \<le> i_4"
  assumes fact5: "region (base a) \<le> (0 :: int)"
  assumes fact6: "is_uint32 i"
  assumes fact7: "is_uint32 i_1"
  assumes fact8: "is_uint32 i_2"
  assumes fact9: "is_uint32 i_4"
  assumes fact10: "is_sint32 i_3"
  assumes fact11: "\<forall>(i_5 :: int). is_sint32 i_5 \<longrightarrow> l_count_1' t a i_1 i_2 i_5 + l_count_1' t a i_2 i_4 i_5 = l_count_1' t a i_1 i_4 i_5"
  shows "l_count_1' t a i_1 i_2 i_3 + l_count_1' t a i_2 i_4 i_3 = l_count_1' t a i_1 i_4 i_3"
  sorry
end
