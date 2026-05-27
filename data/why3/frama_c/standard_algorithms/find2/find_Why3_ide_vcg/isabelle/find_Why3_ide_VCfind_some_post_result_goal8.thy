theory find_Why3_ide_VCfind_some_post_result_goal8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_find2_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_find2_lib.Axiomatic_Axiomatic"
begin
theorem goal8:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  shows "let x :: int = t_1 (shift a i_2) in i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_1 \<le> i_2 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> p_hasvalue_1' t_1 a (0 :: int) i_1 i \<longrightarrow> \<not>p_hasvalue_1' t_1 a (0 :: int) i_2 i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> x = i"
  sorry
end
