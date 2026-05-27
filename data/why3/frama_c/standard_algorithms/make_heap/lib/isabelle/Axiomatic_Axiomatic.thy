theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_unchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_unchanged_1' mint_0 mint_1 a m n \<longleftrightarrow> (\<forall>(i :: int). let a_1 :: addr = shift a i in m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 a_1 = mint_0 a_1)" for mint_0 mint_1 a m n
definition l_heapparent :: "int \<Rightarrow> int"
  where "l_heapparent i = (i - (1 :: int)) cdiv (2 :: int)" for i
definition p_isheap :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_isheap mint_0 a n \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) < i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift a i) \<le> mint_0 (shift a (l_heapparent i)))" for mint_0 a n
end
