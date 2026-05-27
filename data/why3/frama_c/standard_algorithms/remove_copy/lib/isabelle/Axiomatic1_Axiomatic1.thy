theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_Count_A_Count" "Why3STD.Cint_Cint" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_multisetretainrest_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetretainrest_1' mint_0 mint_1 a m1_0 m2_0 b n1_0 n2_0 v \<longleftrightarrow> (\<forall>(i :: int). \<not>i = v \<longrightarrow> is_sint32 i \<longrightarrow> l_count_1' mint_1 a m1_0 m2_0 i = l_count_1' mint_0 b n1_0 n2_0 i)" for mint_0 mint_1 a m1_0 m2_0 b n1_0 n2_0 v
end
