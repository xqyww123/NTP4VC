theory find_first_of_Why3_ide_VCfind_first_of_assert_rte_unsigned_overflow_goal5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_first_of_lib.Compound_Compound" "frama_c_standard_algorithms_find_first_of_lib.Axiomatic_Axiomatic"
begin
theorem goal5:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_1; x :: int = t_1 a_2 in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 (t_1 (shift a i_2)) \<longrightarrow> is_sint32 x \<longrightarrow> \<not>p_hasvalueof t_1 a_1 i_1 a i_2 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> \<not>p_hasvalue_1' t_1 a (0 :: int) i_2 x \<longrightarrow> i_1 \<le> (4294967294 :: int)"
  sorry
end
