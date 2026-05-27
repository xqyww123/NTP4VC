theory Axiomatic12_Axiomatic12
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_bmatch :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_bmatch mint_0 b1_0 b2_0 n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift b2_0 i) = mint_0 (shift b1_0 i))" for mint_0 b1_0 b2_0 n
end
