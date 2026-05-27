theory memscan_Why3_ide_VCmemscan_found_post_goal14
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal14:
  fixes a_7 :: "addr"
  fixes a_10 :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes i_1 :: "int"
  fixes a_6 :: "addr"
  fixes a_12 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_5 :: "addr"
  fixes a_3 :: "addr"
  fixes a_11 :: "addr"
  fixes a_9 :: "addr"
  fixes a_8 :: "addr"
  shows "let x :: int = offset a_7; x_1 :: int = offset a_10; x_2 :: int = i + x_1; x_3 :: int = t_1 (shift a_2 i_1); x_4 :: int = i + x_1 - x in base a_10 = base a_6 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> (0 :: int) \<le> i_1 \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_12) \<le> (0 :: int) \<longrightarrow> i_1 + x < x_2 \<longrightarrow> linked t \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_4 a_10 \<longrightarrow> is_sint32 x_3 \<longrightarrow> is_uint64 x_4 \<longrightarrow> valid_rd t (shift a (0 :: int)) x_4 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_4 \<longrightarrow> addr_le a_10 (shift a_5 x_4) \<longrightarrow> i = (0 :: int) \<or> x_3 = t_1 a_10 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x < x_1 \<longrightarrow> \<not>t_1 (shift a_3 i_2) = x_3) \<longrightarrow> (\<exists>(i_2 :: int). shift a_12 i_2 = a_11 \<and> t_1 (shift a_9 i_2) = x_3 \<and> (0 :: int) \<le> i_2 \<and> i_2 + x < x_2 \<and> (\<forall>(i_3 :: int). (0 :: int) \<le> i_3 \<longrightarrow> i_3 < i_2 \<longrightarrow> \<not>t_1 (shift a_8 i_3) = x_3))"
  sorry
end
