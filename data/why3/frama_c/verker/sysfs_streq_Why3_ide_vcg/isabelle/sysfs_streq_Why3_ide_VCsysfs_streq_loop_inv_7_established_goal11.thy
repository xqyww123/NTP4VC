theory sysfs_streq_Why3_ide_VCsysfs_streq_loop_inv_7_established_goal11
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_StrnCmp_A_StrnCmp" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal11:
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes t_1 :: "addr \<Rightarrow> int"
  assumes fact0: "region (base a) \<le> (0 :: int)"
  assumes fact1: "region (base a_1) \<le> (0 :: int)"
  assumes fact2: "linked t"
  assumes fact3: "sconst t_1"
  assumes fact4: "p_valid_str t t_1 a"
  assumes fact5: "p_valid_str t t_1 a_1"
  shows "p_strnequal t_1 a_1 a (0 :: int)"
  sorry
end
