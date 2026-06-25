theory linked_list_rev_InPlaceRevSeq_list_seg_appendqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
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
typedecl 'a memory
typedecl  "next"
definition list_seg :: "(loc \<Rightarrow> loc) \<Rightarrow> loc \<Rightarrow> loc list \<Rightarrow> loc \<Rightarrow> _"
  where "list_seg next1 p s q \<longleftrightarrow> (let n :: int = int (length s) in (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n \<longrightarrow> \<not>s ! nat i = null) \<and> (p = q \<and> n = (0 :: int) \<or> (1 :: int) \<le> n \<and> s ! (0 :: nat) = p \<and> next1 (s ! nat (n - (1 :: int))) = q \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < n - (1 :: int) \<longrightarrow> next1 (s ! nat i) = s ! nat (i + (1 :: int)))))" for next1 p s q
theorem list_seg_append'vc:
  fixes next1 :: "loc \<Rightarrow> loc"
  fixes p :: "loc"
  fixes pM :: "loc list"
  fixes q :: "loc"
  fixes qM :: "loc list"
  fixes r :: "loc"
  assumes fact0: "list_seg next1 p pM q"
  assumes fact1: "list_seg next1 q qM r"
  shows "list_seg next1 p (pM @ qM) r"
  sorry
end
