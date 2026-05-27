theory mismatch_Why3_ide_VCmismatch_loop_inv_bound_preserved_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_mismatch_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_mismatch_lib.Axiomatic_Axiomatic"
begin
theorem goal0:
  fixes a_1 :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a_1 i_1; x :: int = t_1 a_2; a_3 :: addr = shift a i_1; x_1 :: int = t_1 a_3 in x = x_1 \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i_1 \<le> (4294967294 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 ((1 :: int) + i_1) \<longrightarrow> is_sint32 x_1 \<longrightarrow> is_sint32 x \<longrightarrow> p_equalranges_1' t_1 t_1 a_1 i_1 a \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t a_2 (1 :: int) \<longrightarrow> -(1 :: int) \<le> i_1"
  sorry
end
