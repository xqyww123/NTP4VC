theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_equalranges_2' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_equalranges_2' mint_0 mint_1 a m n b \<longleftrightarrow> (\<forall>(i :: int). m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 (shift a i) = mint_0 (shift b i))" for mint_0 mint_1 a m n b
definition p_unchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_unchanged_1' mint_0 mint_1 a m n \<longleftrightarrow> (\<forall>(i :: int). let a_1 :: addr = shift a i in m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 a_1 = mint_0 a_1)" for mint_0 mint_1 a m n
definition p_equalranges_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_equalranges_1' mint_0 mint_1 a n b \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 (shift a i) = mint_0 (shift b i))" for mint_0 mint_1 a n b
end
