theory A_StrPBrk_A_StrPBrk
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_StrSpn_A_StrSpn" "Compound_Compound" "A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
consts l_strpbrk :: "addr \<Rightarrow> addr \<Rightarrow> addr"
axiomatization where Q_strpbrk_base_case:   "l_strpbrk s ct_0 = Mk_addr (0 :: int) (0 :: int)"
 if "mchar_0 s = (0 :: int)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and ct_0 :: "addr"
axiomatization where Q_strpbrk_found:   "\<not>mchar_0 s = (0 :: int) \<longrightarrow> p_in_array mchar_0 ct_0 (mchar_0 s) \<longrightarrow> l_strpbrk s ct_0 = s"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and ct_0 :: "addr"
axiomatization where Q_strpbrk_not_found:   "\<not>mchar_0 s = (0 :: int) \<longrightarrow> \<not>p_in_array mchar_0 ct_0 (mchar_0 s) \<longrightarrow> l_strpbrk (shift s (1 :: int)) ct_0 = l_strpbrk s ct_0"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and ct_0 :: "addr"
end
