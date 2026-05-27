theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_constantrange :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_constantrange mint_0 a first_0 last_0 val_0 \<longleftrightarrow> (\<forall>(i :: int). first_0 \<le> i \<longrightarrow> i < last_0 \<longrightarrow> mint_0 (shift a i) = val_0)" for mint_0 a first_0 last_0 val_0
end
