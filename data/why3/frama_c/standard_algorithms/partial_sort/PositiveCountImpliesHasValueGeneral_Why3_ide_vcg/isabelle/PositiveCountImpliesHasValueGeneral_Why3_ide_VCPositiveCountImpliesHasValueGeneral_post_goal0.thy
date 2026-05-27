theory PositiveCountImpliesHasValueGeneral_Why3_ide_VCPositiveCountImpliesHasValueGeneral_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic1_Axiomatic1"
begin
theorem goal0:
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes p :: "bool"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "(0 :: int) < l_count_1' t a i_1 i i_2"
  assumes fact2: "is_uint32 i"
  assumes fact3: "is_uint32 i_1"
  assumes fact4: "is_uint32 i_3"
  assumes fact5: "is_sint32 i_2"
  assumes fact6: "i \<le> i_1 \<or> p = False \<and> i_3 \<le> i \<and> i \<le> i_3 \<and> i_1 \<le> i_3 \<and> (\<forall>(i_4 :: int). is_sint32 i_4 \<longrightarrow> (\<forall>(i_5 :: int). i_1 \<le> i_5 \<longrightarrow> i_5 < i_3 \<longrightarrow> \<not>t (shift a i_5) = i_4) \<longrightarrow> l_count_1' t a i_1 i_3 i_4 = (0 :: int))"
  shows "p_hasvalue_1' t a i_1 i i_2"
  sorry
end
