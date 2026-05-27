theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_hasvalue_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_hasvalue_1' mint_0 a m n v \<longleftrightarrow> (\<exists>(i :: int). mint_0 (shift a i) = v \<and> m \<le> i \<and> i < n)" for mint_0 a m n v
end
