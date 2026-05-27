theory upper_bound_Why3_ide_VCupper_bound_loop_term_decrease_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_upper_bound_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_upper_bound_lib.Compound_Compound"
begin
theorem goal11:
  fixes i_1 :: "int"
  fixes i_4 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_5 :: "int"
  fixes i :: "int"
  shows "let x_1 :: int = i_1 - i_4; x_2 :: int = i_4 + to_uint32 (to_uint32 x_1 cdiv (2 :: int)); x_3 :: int = i_4 + x_1 cdiv (2 :: int); a_1 :: addr = shift a x_3; x_4 :: int = t_1 a_1; x_5 :: int = (i_2 - i_4) cdiv (2 :: int) in i_4 \<le> i_1 \<longrightarrow> i_1 \<le> i_3 \<longrightarrow> (0 :: int) \<le> i_4 \<longrightarrow> i_4 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> (0 :: int) \<le> x_2 \<longrightarrow> i_1 \<le> (4294967295 :: int) + i_4 \<longrightarrow> x_2 \<le> (4294967295 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_uint32 i_5 \<longrightarrow> is_sint32 i \<longrightarrow> p_sorted_1' t_1 a (0 :: int) i_3 \<longrightarrow> p_upperbound_1' t_1 a (0 :: int) i_4 i \<longrightarrow> p_strictlowerbound_1' t_1 a i_1 i_3 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i_3 \<longrightarrow> is_uint32 x_3 \<longrightarrow> is_sint32 x_4 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> (if x_4 \<le> i then i_2 = i_1 \<and> (1 :: int) + i_4 + x_5 = i_5 \<and> i_4 + x_5 \<le> (4294967294 :: int) else i_5 = i_4 \<and> i_5 + (i_1 - i_5) cdiv (2 :: int) = i_2) \<longrightarrow> i_2 + i_4 < i_1 + i_5"
  sorry
end
