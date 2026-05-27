theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_weaklysorted_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_weaklysorted_1' mint_0 a m n \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> (2 :: int) + i \<le> n \<longrightarrow> mint_0 (shift a i) \<le> mint_0 (shift a ((1 :: int) + i)))" for mint_0 a m n
definition p_sorted_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_sorted_1' mint_0 a m n \<longleftrightarrow> (\<forall>(i_1 :: int) (i :: int). i < n \<longrightarrow> m \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> mint_0 (shift a i_1) \<le> mint_0 (shift a i))" for mint_0 a m n
end
