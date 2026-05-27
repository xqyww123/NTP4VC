theory max_seq_Why3_ide_VCmax_seq_post_2_goal1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_standard_algorithms_max_seq_lib.Axiomatic_Axiomatic" "frama_c_standard_algorithms_max_seq_lib.Compound_Compound"
begin
theorem goal1:
  fixes a :: "addr"
  fixes i_1 :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_1 :: addr = shift a i_1; x :: int = t_1 a_1 in (0 :: int) < i \<longrightarrow> i_1 \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint32 i_1 \<longrightarrow> p_maxelement t_1 a i i_1 \<longrightarrow> is_sint32 x \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t a_1 (1 :: int) \<longrightarrow> p_strictupperbound_1' t_1 a (0 :: int) i_1 x \<longrightarrow> (\<exists>(i_2 :: int). x = t_1 (shift a i_2) \<and> (0 :: int) \<le> i_2 \<and> i_2 < i)"
  sorry
end
