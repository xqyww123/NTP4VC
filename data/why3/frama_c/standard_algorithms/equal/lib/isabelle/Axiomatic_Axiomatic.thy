theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_equalranges_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_equalranges_1' mint_0 mint_1 a n b \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 (shift a i) = mint_0 (shift b i))" for mint_0 mint_1 a n b
end
