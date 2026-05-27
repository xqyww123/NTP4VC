theory max_seq_Why3_ide_VCmax_seq_assert_rte_mem_access_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_max_seq_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_max_seq_lib.Compound_Compound"
begin
theorem goal2:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i; x :: int = t_1 a_1 in (0 :: int) < i_1 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> i < i_1 \<longrightarrow> i \<le> i_1 \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_maxelement t_1 a i_1 i \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i_1 \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i x \<longrightarrow> valid_rd t a_1 (1 :: int)"
  sorry
end
