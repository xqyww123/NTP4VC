theory equal_range_Why3_ide_VCequal_range_assert_rte_unsigned_overflow_9_goal18
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_equal_range2_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_equal_range2_lib.Compound_Compound"
begin
theorem goal18:
  fixes i_3 :: "int"
  fixes i_4 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_3 - i_4; x_1 :: int = x cdiv (2 :: int); x_2 :: int = i_4 + x_1; a_1 :: addr = shift a x_2; x_3 :: int = t_1 a_1; x_4 :: int = i_4 + to_uint32 (to_uint32 x cdiv (2 :: int)); a_2 :: addr = shift a i_4 in (0 :: int) \<le> i_1 \<longrightarrow> i_3 \<le> i_2 \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> i_1 \<le> x_1 \<longrightarrow> x_3 \<le> i \<longrightarrow> (0 :: int) \<le> x_4 \<longrightarrow> i \<le> x_3 \<longrightarrow> i_3 \<le> (4294967295 :: int) + i_4 \<longrightarrow> x_1 \<le> (4294967295 :: int) \<longrightarrow> x_4 \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_2 \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_4 i \<longrightarrow> p_strictlowerbound_1' t_1 a i_3 i_2 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_2 \<longrightarrow> valid_rd t a_2 x_1 \<longrightarrow> p_sorted_1' t_1 a_2 (0 :: int) x_1 \<longrightarrow> is_uint32 x_2 \<longrightarrow> is_sint32 x_3 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> p_strictupperbound_1' t_1 a_2 (0 :: int) i_1 x_3 \<longrightarrow> p_lowerbound_1' t_1 a_2 i_1 x_1 x_3 \<longrightarrow> i_1 + i_4 \<le> (4294967295 :: int)"
  sorry
end
