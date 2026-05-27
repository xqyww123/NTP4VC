theory PositiveCountImpliesHasValue_Why3_ide_VCPositiveCountImpliesHasValue_loop_inv_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_partial_sort_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_partial_sort_lib.Compound_Compound" "frama_c_standard_algorithms_partial_sort_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = (1 :: int) + i_3 in i_3 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> i_3 < i_1 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) < l_count_1' t a i_2 i_1 i \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x \<longrightarrow> ((\<forall>(i_4 :: int). i_2 \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> \<not>t (shift a i_4) = i) \<longrightarrow> l_count_1' t a i_2 i_3 i = (0 :: int)) \<longrightarrow> i_2 \<le> x"
  sorry
end
