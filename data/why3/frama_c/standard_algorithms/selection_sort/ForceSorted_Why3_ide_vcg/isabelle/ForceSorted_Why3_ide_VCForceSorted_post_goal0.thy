theory ForceSorted_Why3_ide_VCForceSorted_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_selection_sort_lib.Compound_Compound" "frama_c_standard_algorithms_selection_sort_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_selection_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_selection_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "is_uint32 i"
  assumes fact2: "\<forall>(i_2 :: int) (i_1 :: int). i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> t (shift a i_2) \<le> t (shift a i_1)"
  shows "p_sorted_1' t a (0 :: int) i"
  sorry
end
