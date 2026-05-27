theory find_end_Why3_ide_VCfind_end_loop_inv_last_preserved_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find_end_lib.Compound_Compound" "frama_c_standard_algorithms_find_end_lib.Axiomatic_Axiomatic"
begin
theorem goal1:
  fixes a_1 :: "addr"
  fixes i_4 :: "int"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_5 :: "int"
  fixes i_1 :: "int"
  fixes i_3 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let a_2 :: addr = shift a_1 i_4; x :: int = i_2 + i_4; x_1 :: int = i_2 + i_4 - (1 :: int) in (p_equalranges_1' t_1 t_1 a_2 i_2 a \<longleftrightarrow> \<not>i_5 = (0 :: int)) \<longrightarrow> (0 :: int) < i_2 \<longrightarrow> i_1 < i_3 \<longrightarrow> i_2 \<le> i_3 \<longrightarrow> x \<le> i_3 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_4 \<le> (4294967294 :: int) \<longrightarrow> i_3 \<le> (4294967295 :: int) + i_2 \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_uint32 i_3 \<longrightarrow> is_uint32 i_4 \<longrightarrow> is_sint32 i_5 \<longrightarrow> is_uint32 ((1 :: int) + i_4) \<longrightarrow> valid_rd t (shift a (0 :: int)) i_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i_3 \<longrightarrow> valid_rd t a_2 i_2 \<longrightarrow> (if i_5 = (0 :: int) then i_1 = i else i_4 = i_1) \<longrightarrow> (i < i_3 \<longrightarrow> p_equalranges_1' t_1 t_1 (shift a_1 i) i_2 a) \<longrightarrow> (i_3 = i \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 (0 :: int) x_1 a i_2) \<longrightarrow> (i < i_3 \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 ((1 :: int) + i) x_1 a i_2) \<longrightarrow> i_3 = i \<or> i + i_2 \<le> i_3 \<longrightarrow> \<not>p_hassubrange_1' t_1 a_1 ((1 :: int) + i_1) x a i_2"
  sorry
end
