theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_lowerbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_lowerbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> v \<le> mint_0 (shift a i))" for mint_0 a m n v
definition p_strictlowerbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_strictlowerbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> v < mint_0 (shift a i))" for mint_0 a m n v
definition p_minelement :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_minelement mint_0 a n min_0 \<longleftrightarrow> (0 :: int) \<le> min_0 \<and> min_0 < n \<and> p_lowerbound_1' mint_0 a (0 :: int) n (mint_0 (shift a min_0))" for mint_0 a n min_0
end
