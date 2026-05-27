theory sysfs_streq_Why3_ide_VCsysfs_streq_complete_not_trivial_trivial_nulls_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_SysfsStr_A_SysfsStr" "frama_c_verker_lib.A_StrnCmp_A_StrnCmp" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal0:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_1 :: "addr"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = l_sysfs_strlen t_1 a_1; x_1 :: int = l_sysfs_strlen t_1 a in region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> p_valid_str t t_1 a \<longrightarrow> p_valid_str t t_1 a_1 \<longrightarrow> (\<not>x = (0 :: int) \<longleftrightarrow> x_1 = (0 :: int)) \<or> x_1 = (0 :: int) \<and> x = (0 :: int) \<or> \<not>x_1 = (0 :: int) \<and> \<not>x = (0 :: int)"
  sorry
end
