theory HasValueImpliesPositiveCount_Why3_ide_VCHasValueImpliesPositiveCount_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "i_1 \<le> i"
  assumes fact1: "i_3 \<le> i"
  assumes fact2: "i \<le> i_3"
  assumes fact3: "i_1 \<le> i_3"
  assumes fact4: "region (base a) \<le> (0 :: int)"
  assumes fact5: "is_uint32 i"
  assumes fact6: "is_uint32 i_1"
  assumes fact7: "is_uint32 i_3"
  assumes fact8: "is_sint32 i_2"
  assumes fact9: "is_sint32 (t (shift a i_1))"
  assumes fact10: "is_sint32 (t (shift a i_3))"
  assumes fact11: "p_hasvalue_1' t a i_1 i i_2"
  assumes fact12: "\<forall>(i_4 :: int). i_1 \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> (0 :: int) < l_count_1' t a i_1 i (t (shift a i_4))"
  shows "(0 :: int) < l_count_1' t a i_1 i_3 i_2"
  sorry
end
