theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "A_Count_A_Count" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_multisetunchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetunchanged_1' mint_0 mint_1 a first_0 last_0 \<longleftrightarrow> (\<forall>(i :: int). is_sint32 i \<longrightarrow> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i)" for mint_0 mint_1 a first_0 last_0
definition p_sorted_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_sorted_1' mint_0 a m n \<longleftrightarrow> (\<forall>(i_1 :: int) (i :: int). i < n \<longrightarrow> m \<le> i_1 \<longrightarrow> i_1 < i \<longrightarrow> mint_0 (shift a i_1) \<le> mint_0 (shift a i))" for mint_0 a m n
definition l_heapparent :: "int \<Rightarrow> int"
  where "l_heapparent i = (i - (1 :: int)) cdiv (2 :: int)" for i
definition p_isheap :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_isheap mint_0 a n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) < i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) \<le> mint_0 (shift a (l_heapparent i)))" for mint_0 a n
end
