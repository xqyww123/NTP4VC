theory equal_range_Why3_ide_VCequal_range_loop_inv_bounds_preserved_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_equal_range2_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_equal_range2_lib.Compound_Compound"
begin
theorem goal4:
  fixes i_3 :: "int"
  fixes i_5 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_4 :: "int"
  fixes i_6 :: "int"
  fixes a_1 :: "addr"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t_2 :: "addr \<Rightarrow> int"
  shows "let x_1 :: int = i_3 - i_5; x_2 :: int = i_5 + to_uint32 (to_uint32 x_1 cdiv (2 :: int)); x_3 :: int = i_5 + x_1 cdiv (2 :: int); a_2 :: addr = shift a x_3; x_4 :: int = t_1 a_2; x_5 :: int = (i_4 - i_5) cdiv (2 :: int); x_6 :: int = i_6 + (i_3 - i_6) cdiv (2 :: int); a_3 :: addr = shift a_1 x_6 in i_3 \<le> i_2 \<longrightarrow> i_5 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_5 \<longrightarrow> i_5 < i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> i_3 \<le> (4294967295 :: int) + i_5 \<longrightarrow> x_2 \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_uint32 i_6 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 i_1 \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_2 \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_5 i \<longrightarrow> p_strictlowerbound_1' t_1 a i_3 i_2 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_2 \<longrightarrow> is_uint32 x_3 \<longrightarrow> is_sint32 x_4 \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> (if x_4 < i then i_4 = i_3 \<and> (1 :: int) + i_5 + x_5 = i_6 \<and> i_5 + x_5 \<le> (4294967294 :: int) else i_1 = i \<and> i_6 = i_5 \<and> a_1 = a \<and> t_2 = t_1 \<and> x_6 = i_4 \<and> i_1 < t_2 a_3 \<and> valid_rd t a_3 (1 :: int)) \<longrightarrow> i_4 \<le> i_2 \<and> i_6 \<le> i_4 \<and> (0 :: int) \<le> i_6"
  sorry
end
