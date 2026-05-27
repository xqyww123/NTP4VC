theory search_Why3_ide_VCsearch_post_result_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_search_lib.Compound_Compound" "frama_c_standard_algorithms_search_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_2 :: "int"
  fixes i_4 :: "int"
  fixes p_1 :: "bool"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes p :: "bool"
  shows "let x :: int = i_1 + i_3; a_2 :: addr = shift a_1 i in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i_4 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2 \<longrightarrow> (if i_1 \<le> i_2 then p_1 = False \<and> i_2 \<le> (4294967295 :: int) + i_1 \<and> x \<le> (1 :: int) + i_2 \<and> \<not>p_hassubrange_1' t_1 a_1 (0 :: int) (i_1 + i_3 - (1 :: int)) a i_1 \<and> (if x \<le> i_2 then p = False \<and> i_3 = i \<and> \<not>i_4 = (0 :: int) \<and> valid_rd t a_2 i_1 \<and> p_equalranges_1' t_1 t_1 a_2 i_1 a else i_2 = i) else i_2 = i) \<longrightarrow> (0 :: int) \<le> i \<and> i \<le> i_2"
  sorry
end
