theory max_element_Why3_ide_VCmax_element_assert_rte_unsigned_overflow_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_max_element2_lib.Compound_Compound" "frama_c_standard_algorithms_max_element2_lib.Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a (0 :: int); a_2 :: addr = shift a i_1; x :: int = t_1 a_2; a_3 :: addr = shift a i_2 in (0 :: int) < i \<longrightarrow> i_2 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 (t_1 a_1) \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 (t_1 a_3) \<longrightarrow> valid_rd t a_1 i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> p_upperbound_1' t_1 a (0 :: int) i_2 x \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_1 x \<longrightarrow> i_2 \<le> (4294967294 :: int)"
  sorry
end
