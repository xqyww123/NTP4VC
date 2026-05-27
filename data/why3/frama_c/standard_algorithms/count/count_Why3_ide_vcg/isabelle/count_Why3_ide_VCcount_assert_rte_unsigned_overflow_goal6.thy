theory count_Why3_ide_VCcount_assert_rte_unsigned_overflow_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_count_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_count_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_count_lib.Compound_Compound" "frama_c_standard_algorithms_count_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_1; x :: int = t_1 a_1; x_1 :: int = l_count_1' t_1 a (0 :: int) i_1 x in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x_1 \<le> i_1 \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_uint32 x_1 \<longrightarrow> x_1 \<le> (4294967294 :: int)"
  sorry
end
