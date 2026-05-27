theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "A_DifferenceAxiomatic_A_DifferenceAxiomatic" "Why3STD.Cint_Cint" "Axiomatic_Axiomatic"
begin
definition p_adjacentdifference :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_adjacentdifference mint_0 a n b \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift b i) = l_difference mint_0 a i)" for mint_0 a n b
definition p_adjacentdifferencebounds :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_adjacentdifferencebounds mint_0 a n \<longleftrightarrow> (\<forall>(i :: int). let x :: int = l_difference mint_0 a i in (0 :: int) < i \<longrightarrow> i < n \<longrightarrow> -(2147483648 :: int) \<le> x \<and> x \<le> (2147483647 :: int))" for mint_0 a n
end
