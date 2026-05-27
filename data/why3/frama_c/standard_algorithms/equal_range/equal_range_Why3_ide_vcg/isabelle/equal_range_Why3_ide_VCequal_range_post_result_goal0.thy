theory equal_range_Why3_ide_VCequal_range_post_result_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_equal_range_lib.S1_size_type_pair_S1_size_type_pair" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_equal_range_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_equal_range_lib.Compound_Compound"
begin
theorem goal0:
  fixes s :: "s1_size_type_pair"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = f1_size_type_pair_first s; x_1 :: int = f1_size_type_pair_second s in x \<le> i_1 \<longrightarrow> x_1 \<le> i_1 \<longrightarrow> (0 :: int) \<le> x \<longrightarrow> (0 :: int) \<le> x_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> iss1_size_type_pair s \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 i \<longrightarrow> is_uint32 x \<longrightarrow> is_uint32 x_1 \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> p_lowerbound_1' t_1 a x i_1 i \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) x i \<longrightarrow> p_upperbound_1' t_1 a (0 :: int) x_1 i \<longrightarrow> p_strictlowerbound_1' t_1 a x_1 i_1 i \<longrightarrow> x \<le> x_1"
  sorry
end
