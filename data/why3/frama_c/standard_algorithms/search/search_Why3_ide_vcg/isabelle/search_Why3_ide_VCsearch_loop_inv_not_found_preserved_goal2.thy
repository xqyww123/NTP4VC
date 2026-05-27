theory search_Why3_ide_VCsearch_loop_inv_not_found_preserved_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_search_lib.Compound_Compound" "frama_c_standard_algorithms_search_lib.Axiomatic_Axiomatic"
begin
theorem goal2:
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  shows "let x :: int = i + i_2; a_2 :: addr = shift a_1 i_2 in i \<le> i_1 \<longrightarrow> x \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_2 \<le> (4294967294 :: int) \<longrightarrow> i_1 \<le> (4294967295 :: int) + i \<longrightarrow> x \<le> (1 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 ((1 :: int) + i_2) \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1 \<longrightarrow> valid_rd t a_2 i \<longrightarrow> \<not>p_equalranges_1' t_1 t_1 a_2 i a \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 (0 :: int) (i + i_2 - (1 :: int)) a i \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 (0 :: int) x a i"
  sorry
end
