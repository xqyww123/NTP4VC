theory esterel_Esterel_intersectionqtvc
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
theorem intersection'vc:
  fixes a :: "s"
  fixes b :: "s"
  shows "let o1 :: int fset = mdl a |\<inter>| mdl b; o2 :: 64 word = bv a AND bv b in (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (64 :: int)) \<and> ((0 \<le> i \<and> bit o2 (nat i))) = True \<longleftrightarrow> i |\<in>| o1) \<and> (\<forall>(result :: s). bv result = o2 \<and> mdl result = o1 \<longrightarrow> mdl result = mdl a |\<inter>| mdl b)"
  sorry
end
