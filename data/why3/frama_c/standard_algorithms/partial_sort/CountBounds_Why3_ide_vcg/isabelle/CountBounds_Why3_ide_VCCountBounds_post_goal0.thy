theory CountBounds_Why3_ide_VCCountBounds_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic1_Axiomatic1"
begin
theorem goal0:
  fixes t :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes i_1 :: "int"
  shows "let x :: int = l_count_1' t a (0 :: int) i i_1 in (0 :: int) \<le> i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> is_uint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> (\<forall>(i_2 :: int). let x_1 :: int = l_count_1' t a (0 :: int) i i_2 in is_sint32 i_2 \<longrightarrow> x_1 \<le> i \<and> (0 :: int) \<le> x_1) \<longrightarrow> x \<le> i \<and> (0 :: int) \<le> x"
  sorry
end
