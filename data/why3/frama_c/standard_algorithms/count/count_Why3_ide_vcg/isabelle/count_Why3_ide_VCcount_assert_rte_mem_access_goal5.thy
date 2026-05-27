theory count_Why3_ide_VCcount_assert_rte_mem_access_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_count_lib.Axiomatic1_Axiomatic1" "frama_c_standard_algorithms_count_lib.A_Count_A_Count" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_count_lib.Compound_Compound" "frama_c_standard_algorithms_count_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_count_1' t_1 a (0 :: int) i_2 i in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> x \<le> i_2 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> is_uint32 x \<longrightarrow> valid_rd t (shift a i_2) (1 :: int)"
  sorry
end
