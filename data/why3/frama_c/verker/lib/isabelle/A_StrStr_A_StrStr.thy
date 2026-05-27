theory A_StrStr_A_StrStr
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_Strlen_A_Strlen" "Compound_Compound" "Why3STD.Cint_Cint"
begin
consts l_strstr :: "addr \<Rightarrow> addr \<Rightarrow> addr"
definition p_strmatch :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> _"
  where "p_strmatch mchar_0 s1_0 s2_0 \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < l_strlen mchar_0 s2_0 \<longrightarrow> mchar_0 (shift s2_0 i) = mchar_0 (shift s1_0 i))" for mchar_0 s1_0 s2_0
end
