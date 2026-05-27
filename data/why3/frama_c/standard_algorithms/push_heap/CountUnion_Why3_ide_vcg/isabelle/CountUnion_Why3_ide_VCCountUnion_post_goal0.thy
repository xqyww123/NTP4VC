theory CountUnion_Why3_ide_VCCountUnion_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_push_heap_lib.A_Count_A_Count" "frama_c_standard_algorithms_push_heap_lib.Compound_Compound" "frama_c_standard_algorithms_push_heap_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_push_heap_lib.Axiomatic1_Axiomatic1"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 \<le> i"
  assumes fact1: "(0 :: int) \<le> i_1"
  assumes fact2: "region (base a) \<le> (0 :: int)"
  assumes fact3: "is_uint32 i"
  assumes fact4: "is_uint32 i_1"
  assumes fact5: "is_sint32 i_2"
  assumes fact6: "\<forall>(i_3 :: int). is_sint32 i_3 \<longrightarrow> l_count_1' t a (0 :: int) i_1 i_3 + l_count_1' t a i_1 i i_3 = l_count_1' t a (0 :: int) i i_3"
  shows "l_count_1' t a (0 :: int) i_1 i_2 + l_count_1' t a i_1 i i_2 = l_count_1' t a (0 :: int) i i_2"
  sorry
end
