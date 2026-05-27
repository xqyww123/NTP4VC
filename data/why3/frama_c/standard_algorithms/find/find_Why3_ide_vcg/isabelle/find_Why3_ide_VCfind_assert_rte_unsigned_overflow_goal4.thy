theory find_Why3_ide_VCfind_assert_rte_unsigned_overflow_goal4
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_standard_algorithms_find_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal4:
  fixes a :: "addr"
  fixes i_2 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_2; x :: int = t_1 a_1 in \<not>x = i \<longrightarrow> i_2 \<le> i_1 \<longrightarrow> (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i_1 \<longrightarrow> is_uint32 i_2 \<longrightarrow> is_sint32 i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> \<not>t_1 (shift a i_3) = i) \<longrightarrow> i_2 \<le> (4294967294 :: int)"
  sorry
end
