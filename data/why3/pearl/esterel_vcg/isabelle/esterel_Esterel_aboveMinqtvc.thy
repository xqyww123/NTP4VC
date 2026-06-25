theory esterel_Esterel_aboveMinqtvc
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
theorem aboveMin'vc:
  fixes a :: "s"
  assumes fact0: "\<not>mdl a = fempty"
  shows "let res :: 64 word = bv a OR -bv a; o1 :: int fset = Ico_fset_int (Min (fset (mdl a))) (64 :: int) in (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (64 :: int)) \<and> ((0 \<le> i \<and> bit res (nat i))) = True \<longleftrightarrow> i |\<in>| o1) \<and> (\<forall>(result :: s). bv result = res \<and> mdl result = o1 \<longrightarrow> mdl result = Ico_fset_int (Min (fset (mdl a))) (64 :: int))"
  sorry
end
