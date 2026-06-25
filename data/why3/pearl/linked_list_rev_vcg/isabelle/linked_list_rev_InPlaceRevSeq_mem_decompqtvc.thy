theory linked_list_rev_InPlaceRevSeq_mem_decompqtvc
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
theorem mem_decomp'vc:
  fixes x :: "loc"
  fixes s :: "loc list"
  assumes fact0: "x \<in> set s"
  shows "let o1 :: loc = s ! (0 :: nat); o2 :: bool = eq_loc o1 x in (o2 = True \<longleftrightarrow> o1 = x) \<longrightarrow> (if o2 = True then (0 :: int) \<le> (1 :: int) \<and> (1 :: int) \<le> int (length s) else ((0 :: int) \<le> (1 :: int) \<and> (1 :: int) \<le> int (length s)) \<and> (let o3 :: loc list = drop (1 :: nat) s in ((0 :: int) \<le> int (length s) \<and> length o3 < length s) \<and> x \<in> set o3)) \<and> (\<forall>(s1 :: loc list) (s2 :: loc list). (if o2 = True then s1 = [] \<and> s2 = drop (1 :: nat) s else \<exists>(s11 :: loc list). drop (1 :: nat) s = s11 @ Cons x s2 \<and> (let o3 :: loc = s ! (0 :: nat); o4 :: loc list = Cons o3 s11 in (int (length o4) = (1 :: int) + int (length s11) \<and> o4 ! (0 :: nat) = o3 \<and> (\<forall>(i :: int). (0 :: int) < i \<and> i \<le> int (length s11) \<longrightarrow> o4 ! nat i = s11 ! nat (i - (1 :: int)))) \<and> s1 = o4)) \<longrightarrow> s = s1 @ Cons x s2)"
  sorry
end
