theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_hasequalneighbors :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_hasequalneighbors mint_0 a n \<longleftrightarrow> (\<exists>(i :: int). mint_0 (shift a ((1 :: int) + i)) = mint_0 (shift a i) \<and> (0 :: int) \<le> i \<and> (2 :: int) + i \<le> n)" for mint_0 a n
end
