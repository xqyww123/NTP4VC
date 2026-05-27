theory memscan_Why3_ide_VCmemscan_not_exists_post_goal15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal15:
  fixes a_7 :: "addr"
  fixes a_8 :: "addr"
  fixes i :: "int"
  fixes a_6 :: "addr"
  fixes a_10 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes a_4 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_5 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  fixes a_9 :: "addr"
  shows "let x :: int = offset a_7; x_1 :: int = offset a_8; x_2 :: int = i + x_1 - x in base a_8 = base a_6 \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> x \<le> x_1 \<longrightarrow> region (base a_10) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_sint32 i_1 \<longrightarrow> is_uint64 i \<longrightarrow> addr_le a_4 a_8 \<longrightarrow> is_uint64 x_2 \<longrightarrow> valid_rd t (shift a (0 :: int)) x_2 \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) x_2 \<longrightarrow> addr_le a_8 (shift a_5 x_2) \<longrightarrow> i = (0 :: int) \<or> t_1 a_8 = i_1 \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x < i + x_1 \<longrightarrow> \<not>t_1 (shift a_2 i_2) = i_1) \<longrightarrow> (\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 + x < x_1 \<longrightarrow> \<not>t_1 (shift a_3 i_2) = i_1) \<longrightarrow> shift a_10 x_2 = a_9"
  sorry
end
