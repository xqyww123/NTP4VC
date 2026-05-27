theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_strictupperbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_strictupperbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) < v)" for mint_0 a m n v
definition p_upperbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_upperbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) \<le> v)" for mint_0 a m n v
definition p_maxelement :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_maxelement mint_0 a n max_0 \<longleftrightarrow> (0 :: int) \<le> max_0 \<and> max_0 < n \<and> p_upperbound_1' mint_0 a (0 :: int) n (mint_0 (shift a max_0))" for mint_0 a n max_0
end
