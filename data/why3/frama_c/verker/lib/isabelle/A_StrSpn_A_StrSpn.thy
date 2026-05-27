theory A_StrSpn_A_StrSpn
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "A_Strlen_A_Strlen" "Why3STD.Cint_Cint"
begin
definition p_in_array :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_in_array mchar_0 s c \<longleftrightarrow> (\<exists>(a :: addr). mchar_0 a = c \<and> addr_le s a \<and> addr_lt a (shift s (l_strlen mchar_0 s)))" for mchar_0 s c
consts l_strspn :: "addr \<Rightarrow> addr \<Rightarrow> int"
axiomatization where Q_strspn_base_case:   "l_strspn s accept_0 = (0 :: int)"
 if "mchar_0 s = (0 :: int)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and accept_0 :: "addr"
axiomatization where Q_strspn_not_in_accept:   "\<not>mchar_0 s = (0 :: int) \<longrightarrow> \<not>p_in_array mchar_0 accept_0 (mchar_0 s) \<longrightarrow> l_strspn s accept_0 = (0 :: int)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and accept_0 :: "addr"
axiomatization where Q_strspn_in_accept:   "\<not>mchar_0 s = (0 :: int) \<longrightarrow> p_in_array mchar_0 accept_0 (mchar_0 s) \<longrightarrow> (1 :: int) + l_strspn (shift s (1 :: int)) accept_0 = l_strspn s accept_0"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and accept_0 :: "addr"
end
