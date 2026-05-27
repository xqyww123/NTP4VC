theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_Count_A_Count" "Why3STD.Cint_Cint" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_sorted_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_sorted_1' mint_0 a m n \<longleftrightarrow> (\<forall>(i_1 :: int) (i :: int). i < n \<longrightarrow> m \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> mint_0 (shift a i_1) \<le> mint_0 (shift a i))" for mint_0 a m n
definition p_lowerbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_lowerbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> v \<le> mint_0 (shift a i))" for mint_0 a m n v
definition p_strictlowerbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_strictlowerbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> v < mint_0 (shift a i))" for mint_0 a m n v
definition p_strictupperbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_strictupperbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) < v)" for mint_0 a m n v
definition p_upperbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_upperbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) \<le> v)" for mint_0 a m n v
definition p_minelement :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_minelement mint_0 a n min_0 \<longleftrightarrow> (0 :: int) \<le> min_0 \<and> min_0 < n \<and> p_lowerbound_1' mint_0 a (0 :: int) n (mint_0 (shift a min_0))" for mint_0 a n min_0
definition p_multisetunchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetunchanged_1' mint_0 mint_1 a first_0 last_0 \<longleftrightarrow> (\<forall>(i :: int). is_sint32 i \<longrightarrow> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i)" for mint_0 mint_1 a first_0 last_0
end
