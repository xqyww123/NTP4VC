theory A_MemSet_A_MemSet
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
consts l_memset :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
axiomatization where Q_memset_def:   "(\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mchar_0 (shift s i) = c) \<longleftrightarrow> l_memset mchar_0 s c n = True"
  for n :: "int"
  and mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and c :: "int"
end
