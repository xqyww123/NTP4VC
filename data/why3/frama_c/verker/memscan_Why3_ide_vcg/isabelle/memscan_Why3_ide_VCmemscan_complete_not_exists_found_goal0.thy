theory memscan_Why3_ide_VCmemscan_complete_not_exists_found_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal0:
  fixes a_4 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_2 :: "addr"
  fixes a_3 :: "addr"
  assumes fact0: "region (base a_4) \<le> (0 :: int)"
  assumes fact1: "linked t"
  assumes fact2: "is_sint32 i_1"
  assumes fact3: "is_uint64 i"
  assumes fact4: "valid_rd t (shift a (0 :: int)) i"
  assumes fact5: "valid_rd t (shift a_1 (0 :: int)) i"
  shows "(\<forall>(i_2 :: int). (0 :: int) \<le> i_2 \<longrightarrow> i_2 < i \<longrightarrow> \<not>t_1 (shift a_2 i_2) = i_1) \<or> (\<exists>(i_2 :: int). t_1 (shift a_3 i_2) = i_1 \<and> (0 :: int) \<le> i_2 \<and> i_2 < i)"
  sorry
end
