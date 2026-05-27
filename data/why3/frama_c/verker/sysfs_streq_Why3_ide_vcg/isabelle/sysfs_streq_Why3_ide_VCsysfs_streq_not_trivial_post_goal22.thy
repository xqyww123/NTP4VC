theory sysfs_streq_Why3_ide_VCsysfs_streq_not_trivial_post_goal22
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "frama_c_verker_lib.A_Strlen_A_Strlen" "frama_c_verker_lib.Compound_Compound" "Why3STD.Cint_Cint" "frama_c_verker_lib.A_SysfsStr_A_SysfsStr" "frama_c_verker_lib.A_StrnCmp_A_StrnCmp" "frama_c_verker_lib.A_Strnlen_A_Strnlen"
begin
theorem goal22:
  fixes t_1 :: "addr \<Rightarrow> int"
  fixes a_10 :: "addr"
  fixes a_11 :: "addr"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_3 :: "addr"
  fixes a_4 :: "addr"
  fixes a_5 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes a_9 :: "addr"
  fixes i :: "int"
  fixes t :: "int \<Rightarrow> int"
  fixes a_8 :: "addr"
  fixes a_2 :: "addr"
  shows "let x :: int = l_sysfs_strlen t_1 a_10; x_1 :: int = l_sysfs_strlen t_1 a_11; x_2 :: int = t_1 a; x_3 :: int = t_1 a_1; x_4 :: int = t_1 a_3; x_5 :: int = t_1 a_4; x_6 :: int = t_1 a_5; x_7 :: int = t_1 a_6; x_8 :: int = t_1 a_7; x_9 :: int = t_1 a_9; a_12 :: addr = shift a_10 i; x_10 :: int = t_1 a_12; a_13 :: addr = shift a_11 i; x_11 :: int = t_1 a_13; x_12 :: int = (1 :: int) + i; x_13 :: int = l_sysfs_strlen t_1 a_7; x_14 :: int = l_sysfs_strlen t_1 a_1 in \<not>x = (0 :: int) \<longrightarrow> \<not>x_1 = (0 :: int) \<longrightarrow> i \<le> l_strlen t_1 a_10 \<longrightarrow> i \<le> l_strlen t_1 a_11 \<longrightarrow> region (base a_10) \<le> (0 :: int) \<longrightarrow> region (base a_11) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> sconst t_1 \<longrightarrow> is_uint64 i \<longrightarrow> is_sint8 x_2 \<longrightarrow> is_sint8 x_3 \<longrightarrow> is_sint8 x_4 \<longrightarrow> is_sint8 x_5 \<longrightarrow> is_sint8 x_6 \<longrightarrow> is_sint8 x_7 \<longrightarrow> is_sint8 x_8 \<longrightarrow> is_sint8 (t_1 a_8) \<longrightarrow> is_sint8 x_9 \<longrightarrow> p_valid_str t t_1 a_10 \<longrightarrow> p_valid_str t t_1 a_11 \<longrightarrow> p_strnequal t_1 a_11 a_10 i \<longrightarrow> is_sint8 (t_1 (shift a_2 (1 :: int))) \<longrightarrow> is_sint8 (t_1 (shift a_4 (1 :: int))) \<longrightarrow> is_sint8 x_10 \<longrightarrow> is_sint8 x_11 \<longrightarrow> p_valid_str t t_1 a_12 \<longrightarrow> p_valid_str t t_1 a_13 \<longrightarrow> (if x_11 = (0 :: int) then \<forall>(i_1 :: int). let x_15 :: int = t_1 (shift a_10 i_1); x_16 :: int = t_1 (shift a_11 i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> is_uint64 i_1 \<longrightarrow> \<not>x_15 = (0 :: int) \<and> \<not>x_16 = (0 :: int) \<and> x_16 = x_15 else \<not>x_7 = x_2 \<and> a_12 = a \<and> a_13 = a_6 \<and> (\<forall>(i_1 :: int). let x_15 :: int = t_1 (shift a_10 i_1); x_16 :: int = t_1 (shift a_11 i_1) in (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> is_uint64 i_1 \<longrightarrow> \<not>x_15 = (0 :: int) \<and> \<not>x_16 = (0 :: int) \<and> x_16 = x_15)) \<longrightarrow> (if x_11 = x_10 then x_6 = (0 :: int) \<and> x_9 = (0 :: int) \<and> a_12 = a_5 \<and> a_13 = a_9 \<and> x_1 = x else a_13 = a_7 \<and> (if x_8 = (0 :: int) then a_12 = a_1 \<and> (if x_3 = (10 :: int) then a_2 = a_1 \<and> (if t_1 (shift a_10 x_12) = (0 :: int) then x_13 = x_14 \<and> x = i \<and> p_strnequal t_1 a_7 a_1 x_14 else a_4 = a_1 \<and> a_8 = a_7) else a_4 = a_1 \<and> a_8 = a_7) else a_8 = a_7 \<and> (if x_8 = (10 :: int) then if t_1 (shift a_11 x_12) = (0 :: int) then a_12 = a_3 \<and> (if x_4 = (0 :: int) then x_13 = l_sysfs_strlen t_1 a_3 \<and> x_1 = i \<and> p_strnequal t_1 a_7 a_3 x_13 else a_4 = a_3 \<and> \<not>x_4 = (10 :: int)) else a_12 = a_4 \<and> (\<not>x_5 = (0 :: int) \<longrightarrow> \<not>x_5 = (10 :: int)) else a_12 = a_4 \<and> (\<not>x_5 = (0 :: int) \<longrightarrow> \<not>x_8 = x_5)))) \<longrightarrow> (\<forall>(i_1 :: int). (0 :: int) \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> t_1 (shift a_11 i_1) = t_1 (shift a_10 i_1)) \<longrightarrow> p_strnequal t_1 a_11 a_10 (to_uint64 (min x x_1))"
  sorry
end
