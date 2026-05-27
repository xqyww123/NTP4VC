theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_InnerProductAxiomatic_A_InnerProductAxiomatic" "Why3STD.Cint_Cint" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_innerproductbounds :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_innerproductbounds mint_0 a b n init_0 \<longleftrightarrow> (\<forall>(i :: int). let x :: int = l_innerproduct mint_0 a b i init_0 in i \<le> n \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> -(2147483648 :: int) \<le> x \<and> x \<le> (2147483647 :: int))" for mint_0 a b n init_0
definition p_productbounds :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_productbounds mint_0 a b n \<longleftrightarrow> (\<forall>(i :: int). let x :: int = mint_0 (shift a i) * mint_0 (shift b i) in (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> -(2147483648 :: int) \<le> x \<and> x \<le> (2147483647 :: int))" for mint_0 a b n
end
