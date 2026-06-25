theory esterel_Esterel_maxUnionqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded"
begin
typedecl  s
consts bv :: "s \<Rightarrow> 64 word"
consts mdl :: "s \<Rightarrow> int fset"
axiomatization where s'invariant:   "((0 :: int) \<le> i \<and> i < (64 :: int)) \<and> ((0 \<le> i \<and> bit (bv self) (nat i))) = True \<longleftrightarrow> i |\<in>| mdl self"
  for i :: "int"
  and self :: "s"
definition s'eq :: "s \<Rightarrow> s \<Rightarrow> _"
  where "s'eq a b \<longleftrightarrow> bv a = bv b \<and> mdl a = mdl b" for a b
axiomatization where s'inj:   "a = b"
 if "s'eq a b"
  for a :: "s"
  and b :: "s"
theorem maxUnion'vc:
  fixes a :: "s"
  fixes b :: "s"
  assumes fact0: "\<not>mdl a = fempty"
  assumes fact1: "\<not>mdl b = fempty"
  shows "\<not>mdl b = fempty"
  and "\<forall>(o1 :: s). mdl o1 = Ico_fset_int (Min (fset (mdl b))) (64 :: int) \<longrightarrow> \<not>mdl a = fempty \<and> (\<forall>(o2 :: s). mdl o2 = Ico_fset_int (Min (fset (mdl a))) (64 :: int) \<longrightarrow> (\<forall>(o3 :: s). mdl o3 = mdl o2 |\<inter>| mdl o1 \<longrightarrow> (\<forall>(o4 :: s). mdl o4 = mdl b |\<union>| mdl a \<longrightarrow> (\<forall>(res :: s). mdl res = mdl o4 |\<inter>| mdl o3 \<longrightarrow> (\<forall>(x :: int). x |\<in>| mdl res \<longleftrightarrow> x |\<in>| mdl a |\<union>| mdl b \<and> max (Min (fset (mdl a))) (Min (fset (mdl b))) \<le> x) \<and> (\<forall>(x :: int). x |\<in>| mdl res \<longleftrightarrow> (\<exists>(y :: int) (z :: int). y |\<in>| mdl a \<and> z |\<in>| mdl b \<and> x = max y z))))))"
  sorry
end
