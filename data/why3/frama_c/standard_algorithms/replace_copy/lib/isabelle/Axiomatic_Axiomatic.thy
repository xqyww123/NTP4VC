theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_replace_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_replace_1' mint_0 mint_1 a n b v w \<longleftrightarrow> (\<forall>(i :: int). let x :: int = mint_1 (shift a i); x_1 :: int = mint_0 (shift b i) in (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> (x = v \<longrightarrow> x_1 = w) \<and> (\<not>x = v \<longrightarrow> x_1 = x))" for mint_0 mint_1 a n b v w
definition p_unchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_unchanged_1' mint_0 mint_1 a m n \<longleftrightarrow> (\<forall>(i :: int). let a_1 :: addr = shift a i in m \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 a_1 = mint_0 a_1)" for mint_0 mint_1 a m n
end
