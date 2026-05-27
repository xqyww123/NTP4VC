theory Axiomatic15_Axiomatic15
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_bound_int32quat :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_bound_int32quat mint_0 q bound_0 \<longleftrightarrow> (let x :: int = mint_0 (shift q (0 :: int)); x_1 :: int = mint_0 (shift q (1 :: int)); x_2 :: int = mint_0 (shift q (2 :: int)); x_3 :: int = mint_0 (shift q (3 :: int)) in x \<le> bound_0 \<and> x_1 \<le> bound_0 \<and> x_2 \<le> bound_0 \<and> x_3 \<le> bound_0 \<and> (0 :: int) \<le> bound_0 + x \<and> (0 :: int) \<le> bound_0 + x_1 \<and> (0 :: int) \<le> bound_0 + x_2 \<and> (0 :: int) \<le> bound_0 + x_3)" for mint_0 q bound_0
end
