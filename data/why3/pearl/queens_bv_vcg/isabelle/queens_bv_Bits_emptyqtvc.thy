theory queens_bv_Bits_emptyqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "./queens_bv_S"
begin
typedecl  t
consts bv :: "t \<Rightarrow> 32 word"
consts mdl :: "t \<Rightarrow> int fset"
axiomatization where t'invariant:   "((0 :: int) \<le> i \<and> i < (32 :: int)) \<and> ((0 \<le> i \<and> bit (bv self) (nat i))) = True \<longleftrightarrow> i |\<in>| mdl self"
  for i :: "int"
  and self :: "t"
definition t'eq :: "t \<Rightarrow> t \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> bv a = bv b \<and> mdl a = mdl b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "t"
  and b :: "t"
theorem empty'vc:
  shows "let o1 :: int fset = fempty in (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (32 :: int)) \<and> ((0 \<le> i \<and> bit (0 :: 32 word) (nat i))) = True \<longleftrightarrow> i |\<in>| o1) \<and> (\<forall>(result :: t). bv result = (0 :: 32 word) \<and> mdl result = o1 \<longrightarrow> mdl result = fempty)"
  sorry
end
