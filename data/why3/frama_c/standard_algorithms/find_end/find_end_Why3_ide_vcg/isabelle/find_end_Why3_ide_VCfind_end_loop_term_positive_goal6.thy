theory find_end_Why3_ide_VCfind_end_loop_term_positive_goal6
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_end_lib.Compound_Compound" "frama_c_standard_algorithms_find_end_lib.Axiomatic_Axiomatic"
begin
theorem goal6:
  fixes a_1 :: "addr"
  fixes i_3 :: "int"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_2 :: addr = shift a_1 i_3; x :: int = i_1 + i_3 - (1 :: int) in (p_equalranges_1' t_1 t_1 a_2 i_1 a \<longleftrightarrow> \<not>i_4 = (0 :: int)) \<longrightarrow> (0 :: int) < i_1 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> i_1 + i_3 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_3 \<le> (4294967294 :: int) \<longrightarrow> i_2 \<le> (4294967295 :: int) + i_1 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_sint32 i_4 \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_2 \<longrightarrow> valid_rd t a_2 i_1 \<longrightarrow> (i < i_2 \<longrightarrow> p_equalranges_1' t_1 t_1 (shift a_1 i) i_1 a) \<longrightarrow> (i_2 = i \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 (0 :: int) x a i_1) \<longrightarrow> (i < i_2 \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 ((1 :: int) + i) x a i_1) \<longrightarrow> i_2 = i \<or> i + i_1 \<le> i_2 \<longrightarrow> i_3 \<le> i_2"
  sorry
end
