theory A_StrCSpn_A_StrCSpn
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_StrSpn_A_StrSpn" "Compound_Compound" "A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
consts l_strcspn :: "addr \<Rightarrow> addr \<Rightarrow> int"
axiomatization where Q_strcspn_base_case:   "l_strcspn s reject_0 = (0 :: int)"
 if "mchar_0 s = (0 :: int)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and reject_0 :: "addr"
axiomatization where Q_strcspn_in_reject:   "\<not>mchar_0 s = (0 :: int) \<longrightarrow> p_in_array mchar_0 reject_0 (mchar_0 s) \<longrightarrow> l_strcspn s reject_0 = (0 :: int)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and reject_0 :: "addr"
axiomatization where Q_strcspn_not_in_reject:   "\<not>mchar_0 s = (0 :: int) \<longrightarrow> \<not>p_in_array mchar_0 reject_0 (mchar_0 s) \<longrightarrow> (1 :: int) + l_strcspn (shift s (1 :: int)) reject_0 = l_strcspn s reject_0"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and reject_0 :: "addr"
end
