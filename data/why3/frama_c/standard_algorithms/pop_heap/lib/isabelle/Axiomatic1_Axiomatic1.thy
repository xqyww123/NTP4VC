theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Axiomatic_Axiomatic" "Compound_Compound" "Why3STD.Cint_Cint" "A_Count_A_Count"
begin
definition p_heapmaximumchild :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_heapmaximumchild mint_0 a n p c \<longleftrightarrow> (let x :: int = l_heapleft p; x_1 :: int = mint_0 (shift a c); x_2 :: int = l_heapright p in (0 :: int) \<le> p \<and> (2 :: int) + p \<le> n \<and> (p \<le> (2147483646 :: int) \<longrightarrow> l_heapparent c = p) \<and> ((2 :: int) + x \<le> n \<longrightarrow> mint_0 (shift a x) \<le> x_1) \<and> ((2 :: int) + x_2 \<le> n \<longrightarrow> mint_0 (shift a x_2) \<le> x_1))" for mint_0 a n p c
definition p_multisetunchanged_1' :: "(addr \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_multisetunchanged_1' mint_0 mint_1 a first_0 last_0 \<longleftrightarrow> (\<forall>(i :: int). is_sint32 i \<longrightarrow> l_count_1' mint_1 a first_0 last_0 i = l_count_1' mint_0 a first_0 last_0 i)" for mint_0 mint_1 a first_0 last_0
end
