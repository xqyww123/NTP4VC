theory CountSectionBounds_Why3_ide_VCCountSectionBounds_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes t :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  shows "let x :: int = l_count_1' t a i_1 i_3 i_2 in i_1 \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> i \<le> i_3 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i_2 \<longrightarrow> (\<forall>(i_4 :: int). let x_1 :: int = l_count_1' t a i_1 i_3 i_4 in is_sint32 i_4 \<longrightarrow> (0 :: int) \<le> x_1 \<and> i_1 + x_1 \<le> i_3) \<longrightarrow> (0 :: int) \<le> x \<and> i_1 + x \<le> i_3"
  sorry
end
