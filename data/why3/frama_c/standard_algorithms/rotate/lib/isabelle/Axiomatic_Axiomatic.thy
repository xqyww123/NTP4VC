theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_reverse_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_reverse_1' mint_0 mint_1 a n b \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_0 (shift b (n - (1 :: int) - i)) = mint_1 (shift a i))" for mint_0 mint_1 a n b
definition p_reverse_2' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_reverse_2' mint_0 mint_1 a m n b p \<longleftrightarrow> p_reverse_1' mint_0 mint_1 (shift a m) (n - m) (shift b p)" for mint_0 mint_1 a m n b p
definition p_reverse_4' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_reverse_4' mint_0 mint_1 a m n p \<longleftrightarrow> p_reverse_2' mint_0 mint_1 a m n a p" for mint_0 mint_1 a m n p
definition p_reverse_5' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_reverse_5' mint_0 mint_1 a m n \<longleftrightarrow> p_reverse_4' mint_0 mint_1 a m n m" for mint_0 mint_1 a m n
definition p_equalranges_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> _"
  where "p_equalranges_1' mint_0 mint_1 a n b \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> mint_1 (shift a i) = mint_0 (shift b i))" for mint_0 mint_1 a n b
definition p_equalranges_3' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_equalranges_3' mint_0 mint_1 a m n b p \<longleftrightarrow> p_equalranges_1' mint_0 mint_1 (shift a m) (n - m) (shift b p)" for mint_0 mint_1 a m n b p
definition p_equalranges_4' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_equalranges_4' mint_0 mint_1 a m n p \<longleftrightarrow> p_equalranges_3' mint_0 mint_1 a m n a p" for mint_0 mint_1 a m n p
end
