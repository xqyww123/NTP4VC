theory CountSectionBounds_Why3_ide_VCCountSectionBounds_loop_inv_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_2 in i_1 \<le> i \<longrightarrow> i_2 \<le> i \<longrightarrow> i_2 < i \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 x \<longrightarrow> (\<forall>(i_3 :: int). let x_1 :: int = l_count_1' t a i_1 i_2 i_3 in is_sint32 i_3 \<longrightarrow> (0 :: int) \<le> x_1 \<and> i_1 + x_1 \<le> i_2) \<longrightarrow> i_1 \<le> x"
  sorry
end
