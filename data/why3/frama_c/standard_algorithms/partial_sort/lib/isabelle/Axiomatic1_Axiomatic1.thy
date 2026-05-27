theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_Count_A_Count" "Why3STD.Cint_Cint" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_hasvalue_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_hasvalue_1' mint_0 a m n v \<longleftrightarrow> (\<exists>(i :: int). mint_0 (shift a i) = v \<and> m \<le> i \<and> i < n)" for mint_0 a m n v
definition p_upperbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_upperbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) \<le> v)" for mint_0 a m n v
definition p_maxelement :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_maxelement mint_0 a n max_0 \<longleftrightarrow> (0 :: int) \<le> max_0 \<and> max_0 < n \<and> p_upperbound_1' mint_0 a (0 :: int) n (mint_0 (shift a max_0))" for mint_0 a n max_0
definition l_heapparent :: "int \<Rightarrow> int"
  where "l_heapparent i = (i - (1 :: int)) cdiv (2 :: int)" for i
definition p_isheap :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_isheap mint_0 a n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) < i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) \<le> mint_0 (shift a (l_heapparent i)))" for mint_0 a n
definition p_multisetunchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetunchanged_1' mint_0 mint_1 a first_0 last_0 \<longleftrightarrow> (\<forall>(i :: int). is_sint32 i \<longrightarrow> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i)" for mint_0 mint_1 a first_0 last_0
definition p_lowerbound_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_lowerbound_1' mint_0 a m n v \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> v \<le> mint_0 (shift a i))" for mint_0 a m n v
definition p_swappedinside :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_swappedinside mint_0 mint_1 a i k n \<longleftrightarrow> (let a_1 :: addr = shift a i; a_2 :: addr = shift a k in mint_1 a_1 = mint_0 a_2 \<and> mint_1 a_2 = mint_0 a_1 \<and> (0 :: int) \<le> i \<and> i < k \<and> k < n \<and> p_unchanged_1' mint_0 mint_1 a (0 :: int) i \<and> p_unchanged_1' mint_0 mint_1 a ((1 :: int) + i) k \<and> p_unchanged_1' mint_0 mint_1 a ((1 :: int) + k) n)" for mint_0 mint_1 a i k n
end
