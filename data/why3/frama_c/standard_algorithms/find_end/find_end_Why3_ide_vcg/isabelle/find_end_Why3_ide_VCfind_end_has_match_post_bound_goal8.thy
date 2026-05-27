theory find_end_Why3_ide_VCfind_end_has_match_post_bound_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_end_lib.Compound_Compound" "frama_c_standard_algorithms_find_end_lib.Axiomatic_Axiomatic"
begin
theorem goal8:
  fixes i :: "int"
  fixes i_2 :: "int"
  fixes i_3 :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes t_2 :: "addr \<Rightarrow> int"
  fixes t_3 :: "addr \<Rightarrow> int"
  shows "let x :: int = i + i_2 - (1 :: int); x_1 :: int = i + i_3 in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_1 \<longrightarrow> p_hassubrange_1' t_1 a_1 (0 :: int) i_1 a i \<longrightarrow> (if (0 :: int) < i then t_2 = t_1 \<and> (if i \<le> i_1 then t_3 = t_2 \<and> i_1 < i + i_2 \<and> i_1 \<le> (4294967295 :: int) + i \<and> (i_3 < i_1 \<longrightarrow> p_equalranges_1' t_3 t_3 (shift a_1 i_3) i a) \<and> (i_3 = i_1 \<longrightarrow> \<not>p_hassubrange_1' t_3 a_1 (0 :: int) x a i) \<and> (i_3 < i_1 \<longrightarrow> \<not>p_hassubrange_1' t_3 a_1 ((1 :: int) + i_3) x a i) \<and> (i_3 = i_1 \<or> x_1 \<le> i_1) else i_3 = i_1) else i_3 = i_1) \<longrightarrow> (0 :: int) \<le> i_3 \<and> x_1 \<le> i_1"
  sorry
end
