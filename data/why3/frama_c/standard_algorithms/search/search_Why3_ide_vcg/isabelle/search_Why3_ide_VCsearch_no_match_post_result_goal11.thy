theory search_Why3_ide_VCsearch_no_match_post_result_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_search_lib.Compound_Compound" "frama_c_standard_algorithms_search_lib.Axiomatic_Axiomatic"
begin
theorem goal11:
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i_2 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = i + i_1; a_2 :: addr = shift a_1 i in \<not>i_3 = (0 :: int) \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> x \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967295 :: int) + i_1 \<longrightarrow> x \<le> (1 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i_3 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2 \<longrightarrow> valid_rd t a_2 i_1 \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 (0 :: int) i_2 a i_1 \<longrightarrow> p_equalranges_1' t_1 t_1 a_2 i_1 a \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 (0 :: int) (i + i_1 - (1 :: int)) a i_1 \<longrightarrow> i_2 = i"
  sorry
end
