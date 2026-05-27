theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "A_Count_A_Count" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_multisetunchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetunchanged_1' mint_0 mint_1 a first_0 last_0 \<longleftrightarrow> (\<forall>(i :: int). is_sint32 i \<longrightarrow> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i)" for mint_0 mint_1 a first_0 last_0
end
