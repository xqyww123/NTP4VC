theory dfs_DFS_setqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
typedecl  loc
consts null :: "loc"
consts root :: "loc"
consts left1 :: "loc \<Rightarrow> loc"
consts right1 :: "loc \<Rightarrow> loc"
typedecl  marks
consts o1 :: "(loc \<Rightarrow> bool) \<Rightarrow> loc \<Rightarrow> bool \<Rightarrow> loc \<Rightarrow> bool"
axiomatization where o1_def:   "o1 m l b x = True \<longleftrightarrow> (if x = l then b = True else m x = True)"
  for m :: "loc \<Rightarrow> bool"
  and l :: "loc"
  and b :: "bool"
  and x :: "loc"
theorem set'vc:
  fixes m :: "loc \<Rightarrow> bool"
  fixes l :: "loc"
  fixes b :: "bool"
  fixes m1 :: "loc \<Rightarrow> bool"
  assumes fact0: "\<forall>(x :: loc). m x = True \<longleftrightarrow> (if x = l then b = True else m1 x = True)"
  shows "m = m1(l := b)"
  sorry
end
