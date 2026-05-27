theory search_n_Why3_ide_VCsearch_n_assert_rte_unsigned_overflow_3_goal10
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_search_n_lib.Compound_Compound" "frama_c_standard_algorithms_search_n_lib.Axiomatic_Axiomatic"
begin
theorem goal10:
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = (1 :: int) + i_3; a_1 :: addr = shift a i_3; x_1 :: int = t_1 a_1; x_2 :: int = t_1 (shift a (i - (1 :: int))) in (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_3 < i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> x \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 x_1 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_2 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> p_constantrange t_1 a i i_3 x_1 \<longrightarrow> \<not>p_hasconstantsubrange t_1 a i_3 i_1 x_1 \<longrightarrow> ((0 :: int) < i \<longrightarrow> \<not>x_2 = x_1) \<longrightarrow> i \<le> to_uint32 x"
  sorry
end
