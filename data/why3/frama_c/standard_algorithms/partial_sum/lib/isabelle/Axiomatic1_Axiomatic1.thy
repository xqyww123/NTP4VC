theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "A_AccumulateAxiomatic_A_AccumulateAxiomatic" "Why3STD.Cint_Cint" "Compound_Compound" "Axiomatic_Axiomatic"
begin
definition p_partialsum :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_partialsum mint_0 a n b \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift b i) = l_accumulate_1' mint_0 a ((1 :: int) + i) (0 :: int))" for mint_0 a n b
definition p_accumulatebounds_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_accumulatebounds_1' mint_0 a n init_0 \<longleftrightarrow> (\<forall>(i :: int). let x :: int = l_accumulate_1' mint_0 a i init_0 in i \<le> n \<longrightarrow> (0 :: int) \<le> i \<longrightarrow> -(2147483648 :: int) \<le> x \<and> x \<le> (2147483647 :: int))" for mint_0 a n init_0
axiomatization where Q_TL_Accumulate_2':   "is_sint32 (l_accumulate_1' mint_0 a n (0 :: int))"
  for mint_0 :: "addr \<Rightarrow> int"
  and a :: "addr"
  and n :: "int"
end
