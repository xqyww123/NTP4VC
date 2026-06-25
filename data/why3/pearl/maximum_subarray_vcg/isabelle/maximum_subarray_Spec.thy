theory maximum_subarray_Spec
  imports "NTP4Verif.NTP4Verif" "Why3STD.int_Sum"
begin
definition maxsublo :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "maxsublo a maxlo s \<longleftrightarrow> (\<forall>(l :: int) (h :: int). (0 :: int) \<le> l \<and> l < maxlo \<longrightarrow> l \<le> h \<and> h \<le> int (length a) \<longrightarrow> sum_list (take (nat h - nat l) (drop (nat l) a)) \<le> s)" for a maxlo s
definition maxsub :: "int list \<Rightarrow> int \<Rightarrow> _"
  where "maxsub a s \<longleftrightarrow> (\<forall>(l :: int) (h :: int). (0 :: int) \<le> l \<and> l \<le> h \<and> h \<le> int (length a) \<longrightarrow> sum_list (take (nat h - nat l) (drop (nat l) a)) \<le> s)" for a s
end
