theory WeaklySortedImpliesSorted_Why3_ide_VCWeaklySortedImpliesSorted_loop_inv_5_preserved_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound"
begin
theorem goal5:
  fixes t :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_3 :: "int"
  shows "let x :: int = t (shift a i_4) in (0 :: int) < i_1 \<longrightarrow> i_2 \<le> i \<longrightarrow> i_4 \<le> i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_2 < i_1 \<longrightarrow> i_3 < i_4 \<longrightarrow> i_4 < i \<longrightarrow> i_1 \<le> i_4 \<longrightarrow> i_2 \<le> i_4 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (1 :: int) + i_3 \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 (i_1 - (1 :: int)) \<longrightarrow> p_sorted_1' t a i_2 i_4 \<longrightarrow> p_weaklysorted_1' t a i_2 i \<longrightarrow> (\<forall>(i_5 :: int). i_1 \<le> i_5 \<longrightarrow> i_5 < i_4 \<longrightarrow> t (shift a i_5) \<le> x) \<longrightarrow> t (shift a i_3) \<le> x"
  sorry
end
