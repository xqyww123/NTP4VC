theory mismatch_Why3_ide_VCmismatch_some_not_equal_post_result_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_mismatch_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_mismatch_lib.Axiomatic_Axiomatic"
begin
theorem goal9:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes a_1 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = t_1 (shift a i_1); x_1 :: int = t_1 (shift a_1 i_1) in i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_sint32 x \<longrightarrow> is_sint32 x_1 \<longrightarrow> \<not>p_equalranges_1' t_1 t_1 a_1 i a \<longrightarrow> p_equalranges_1' t_1 t_1 a_1 i_1 a \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> \<not>x_1 = x"
  sorry
end
