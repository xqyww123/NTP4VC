theory Axiomatic_Axiomatic
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_length_of_str_is :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_length_of_str_is malloc_0 mchar_0 s n \<longleftrightarrow> mchar_0 (shift s n) = (0 :: int) \<and> (0 :: int) \<le> n \<and> valid_rw malloc_0 (shift s (0 :: int)) ((1 :: int) + n) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < n \<longrightarrow> \<not>mchar_0 (shift s i) = (0 :: int))" for malloc_0 mchar_0 s n
end
