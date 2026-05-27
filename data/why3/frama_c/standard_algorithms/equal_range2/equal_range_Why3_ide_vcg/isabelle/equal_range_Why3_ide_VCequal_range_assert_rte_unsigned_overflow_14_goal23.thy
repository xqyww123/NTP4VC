theory equal_range_Why3_ide_VCequal_range_assert_rte_unsigned_overflow_14_goal23
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_equal_range2_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_equal_range2_lib.Compound_Compound"
begin
theorem goal23:
  fixes i_2 :: "int"
  fixes i_5 :: "int"
  fixes i_4 :: "int"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_3 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_2 + i_5; x_2 :: int = i_4 - i_5; x_3 :: int = x_2 cdiv (2 :: int); x_4 :: int = i_5 + x_3; x_5 :: int = i_1 + i_5 + x_3; a_1 :: addr = shift a x_4; x_6 :: int = t_1 a_1; x_7 :: int = i_5 + to_uint32 (to_uint32 x_2 cdiv (2 :: int)); a_2 :: addr = shift a i_5; x_8 :: int = (1 :: int) + i_5 + x_3; a_3 :: addr = shift a x_8; x_9 :: int = i_4 - (1 :: int) - i_5 - x_3 in (0 :: int) \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_4 \<le> i_3 \<longrightarrow> i_5 \<le> i_4 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_4 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_3 \<longrightarrow> i_2 \<le> x_3 \<longrightarrow> x_4 < i_4 \<longrightarrow> x_5 < i_4 \<longrightarrow> x_6 \<le> i \<longrightarrow> (0 :: int) \<le> x_7 \<longrightarrow> i \<le> x_6 \<longrightarrow> x \<le> (4294967295 :: int) \<longrightarrow> i_4 \<le> (4294967295 :: int) + i_5 \<longrightarrow> x_3 \<le> (4294967295 :: int) \<longrightarrow> x_4 \<le> (4294967294 :: int) \<longrightarrow> i_4 \<le> (4294967296 :: int) + i_5 + x_3 \<longrightarrow> x_7 \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_sint32 i \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_3 \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_5 i \<longrightarrow> p_strictlowerbound_1' t_1 a i_4 i_3 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_3 \<longrightarrow> valid_rd t a_2 x_3 \<longrightarrow> p_sorted_1' t_1 a_2 (0 :: int) x_3 \<longrightarrow> is_uint32 x_4 \<longrightarrow> is_uint32 x_8 \<longrightarrow> is_sint32 x_6 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> valid_rd t a_3 x_9 \<longrightarrow> p_sorted_1' t_1 a_3 (0 :: int) x_9 \<longrightarrow> p_strictupperbound_1' t_1 a_2 (0 :: int) i_2 x_6 \<longrightarrow> p_strictlowerbound_1' t_1 a_3 i_1 x_9 x_6 \<longrightarrow> p_lowerbound_1' t_1 a_2 i_2 x_3 x_6 \<longrightarrow> p_upperbound_1' t_1 a_3 (0 :: int) i_1 x_6 \<longrightarrow> x_5 \<le> (4294967294 :: int)"
  sorry
end
