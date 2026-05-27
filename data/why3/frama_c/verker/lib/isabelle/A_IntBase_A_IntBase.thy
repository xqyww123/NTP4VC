theory A_IntBase_A_IntBase
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "A_Ctype_A_Ctype"
begin
definition p_is_hex :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_is_hex mchar_0 s \<longleftrightarrow> mchar_0 (shift s (0 :: int)) = (48 :: int) \<and> l_tolower (mchar_0 (shift s (1 :: int))) = (120 :: int) \<and> p_isxdigit (mchar_0 (shift s (2 :: int)))" for mchar_0 s
definition p_is_oct :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_is_oct mchar_0 s \<longleftrightarrow> mchar_0 (shift s (0 :: int)) = (48 :: int) \<and> \<not>p_is_hex mchar_0 s" for mchar_0 s
definition p_is_dec :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_is_dec mchar_0 s \<longleftrightarrow> \<not>p_is_hex mchar_0 s \<and> \<not>p_is_oct mchar_0 s" for mchar_0 s
end
