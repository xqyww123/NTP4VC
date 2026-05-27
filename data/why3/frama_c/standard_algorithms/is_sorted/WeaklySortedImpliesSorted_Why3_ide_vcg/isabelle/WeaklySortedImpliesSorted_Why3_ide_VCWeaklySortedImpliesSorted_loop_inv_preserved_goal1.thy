theory WeaklySortedImpliesSorted_Why3_ide_VCWeaklySortedImpliesSorted_loop_inv_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_is_sorted_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_is_sorted_lib.Compound_Compound"
begin
theorem goal1:
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "addr \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_3 in i_1 \<le> i \<longrightarrow> i_3 \<le> i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_3 < i \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 x \<longrightarrow> p_sorted_1' t a i_1 i_3 \<longrightarrow> p_weaklysorted_1' t a i_1 i \<longrightarrow> (\<forall>(i_4 :: int). i_2 \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> t (shift a i_4) \<le> t (shift a i_3)) \<longrightarrow> i_2 \<le> x"
  sorry
end
