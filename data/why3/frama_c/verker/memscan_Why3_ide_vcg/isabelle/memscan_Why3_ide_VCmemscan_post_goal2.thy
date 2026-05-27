theory memscan_Why3_ide_VCmemscan_post_goal2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal2:
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes a_10 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_8 :: "addr"
  fixes i :: "int"
  fixes a_5 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes a_3 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_4 :: "addr"
  fixes a_2 :: "addr"
  fixes a_9 :: "addr"
  shows "let x :: int = offset a_6; x_1 :: int = offset a_7; x_2 :: int = base a_10; x_3 :: int = t_1 a_8; x_4 :: int = i + x_1 - x in base a_7 = base a_5 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x \<le> x_1 \<longrightarrow> region x_2 \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_3 a_7 \<longrightarrow> is_uint8 x_3 \<longrightarrow> is_uint64 x_4 \<longrightarrow> valid_rd t (shift a (0 :: int)) x_4 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_4 \<longrightarrow> addr_le a_7 (shift a_4 x_4) \<longrightarrow> i = (0 :: int) \<or> a_8 = a_7 \<and> x_3 = i_1 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x < x_1 \<longrightarrow> \<not>t_1 (shift a_2 i_2) = i_1) \<longrightarrow> x_2 = base a_9"
  sorry
end
