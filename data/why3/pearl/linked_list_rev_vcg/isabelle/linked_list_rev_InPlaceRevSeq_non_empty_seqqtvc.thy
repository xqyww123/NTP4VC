theory linked_list_rev_InPlaceRevSeq_non_empty_seqqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts result :: "'a list \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where result_def:   "result s i = s ! nat (int (length s) - (1 :: int) - i)"
  for s :: "'a list"
  and i :: "int"
typedecl  loc
consts null :: "loc"
consts eq_loc :: "loc \<Rightarrow> loc \<Rightarrow> bool"
axiomatization where eq_loc'spec:   "eq_loc l1 l2 = True \<longleftrightarrow> l1 = l2"
  for l1 :: "loc"
  and l2 :: "loc"
definition disjoint :: "'a list \<Rightarrow> 'a list \<Rightarrow> _"
  where "disjoint s1 s2 \<longleftrightarrow> (\<forall>(i1 :: int). (0 :: int) \<le> i1 \<and> i1 < int (length s1) \<longrightarrow> (\<forall>(i2 :: int). (0 :: int) \<le> i2 \<and> i2 < int (length s2) \<longrightarrow> \<not>s1 ! nat i1 = s2 ! nat i2))" for s1 s2
definition no_repet :: "loc list \<Rightarrow> _"
  where "no_repet s \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> \<not>s ! nat i \<in> set (drop (nat (i + (1 :: int))) s))" for s
theorem non_empty_seq'vc:
  fixes s :: "'a list"
  assumes fact0: "(0 :: int) < int (length s)"
  shows "s = Cons (s ! (0 :: nat)) (drop (1 :: nat) s)"
  sorry
end
