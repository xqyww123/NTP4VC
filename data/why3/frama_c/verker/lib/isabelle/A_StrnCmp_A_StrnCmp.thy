theory A_StrnCmp_A_StrnCmp
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint" "A_Strnlen_A_Strnlen" "A_Strlen_A_Strlen"
begin
consts l_strncmp_2' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int"
axiomatization where fix_l_strncmp_2':   "if n = (0 :: int) then l_strncmp_2' mchar_0 s1_0 s2_0 n = (0 :: int) else if mchar_0 (shift s2_0 (0 :: int)) = mchar_0 (shift s1_0 (0 :: int)) then if mchar_0 (shift s1_0 (0 :: int)) = (0 :: int) then l_strncmp_2' mchar_0 s1_0 s2_0 n = (0 :: int) else l_strncmp_2' mchar_0 (shift s1_0 (1 :: int)) (shift s2_0 (1 :: int)) (to_uint64 (n - (1 :: int))) = l_strncmp_2' mchar_0 s1_0 s2_0 n else to_sint32 (mchar_0 (shift s1_0 (0 :: int)) - mchar_0 (shift s2_0 (0 :: int))) = l_strncmp_2' mchar_0 s1_0 s2_0 n"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s1_0 :: "addr"
  and s2_0 :: "addr"
  and n :: "int"
definition p_strnequal :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_strnequal mchar_0 s1_0 s2_0 n \<longleftrightarrow> l_strncmp_2' mchar_0 s1_0 s2_0 n = (0 :: int)" for mchar_0 s1_0 s2_0 n
axiomatization where Q_TL_strncmp_2':   "is_sint32 (l_strncmp_2' mchar_0 s1_0 s2_0 n)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s1_0 :: "addr"
  and s2_0 :: "addr"
  and n :: "int"
end
