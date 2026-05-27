theory A_SysfsStr_A_SysfsStr
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint" "A_Strlen_A_Strlen" "A_StrnCmp_A_StrnCmp" "A_Strnlen_A_Strnlen"
begin
consts l_sysfs_strlen :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int"
axiomatization where fix_l_sysfs_strlen:   "if mchar_0 (shift s (0 :: int)) = (0 :: int) \<or> mchar_0 (shift s (0 :: int)) = (10 :: int) \<and> mchar_0 (shift s (1 :: int)) = (0 :: int) then l_sysfs_strlen mchar_0 s = (0 :: int) else to_uint64 ((1 :: int) + l_sysfs_strlen mchar_0 (shift s (1 :: int))) = l_sysfs_strlen mchar_0 s"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
axiomatization where Q_TL_sysfs_strlen:   "is_uint64 (l_sysfs_strlen mchar_0 s)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
end
