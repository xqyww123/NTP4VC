theory search_n_Why3_ide_VCsearch_n_assert_rte_unsigned_overflow_5_goal12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_search_n_lib.Compound_Compound" "frama_c_standard_algorithms_search_n_lib.Axiomatic_Axiomatic"
begin
theorem goal12:
  fixes i_4 :: "int"
  fixes a :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i_5 :: "int"
  shows "let x :: int = (1 :: int) + i_4; a_1 :: addr = shift a i_4; x_1 :: int = t_1 a_1; x_2 :: int = t_1 (shift a (i - (1 :: int))); x_3 :: int = to_uint32 x in (0 :: int) < i_2 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> i_4 < i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> i \<le> x \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i_5 \<longrightarrow> is_sint32 x_1 \<longrightarrow> p_constantrange t_1 a i i_4 i_5 \<longrightarrow> \<not>p_hasconstantsubrange t_1 a i_4 i_2 i_5 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_3 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> is_sint32 x_2 \<longrightarrow> (if x_1 = i_5 then i_1 = i \<and> \<not>i_1 + i_2 = x \<and> i_1 \<le> x_3 \<and> i_4 \<le> (4294967294 :: int) \<and> x_3 \<le> (4294967295 :: int) + i_1 else i_4 \<le> (4294967294 :: int)) \<longrightarrow> ((0 :: int) < i \<longrightarrow> \<not>x_2 = i_5) \<longrightarrow> i_4 \<le> (4294967294 :: int)"
  sorry
end
