theory tables_Map_eq_def
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_avl_lib.avl_SelectionTypes"
begin
consts balancing :: "nat"
axiomatization where balancing'def:   "(0 :: int) < int balancing"
typedecl  t
consts le :: "t \<Rightarrow> t \<Rightarrow> bool"
axiomatization where Refl:   "le x x"
  for x :: "t"
axiomatization where Trans:   "le x z"
 if "le x y"
 and "le y z"
  for x :: "t"
  and y :: "t"
  and z :: "t"
consts eq :: "t \<Rightarrow> t \<Rightarrow> bool"
axiomatization where eq_def:   "eq x y \<longleftrightarrow> le x y \<and> le y x"
  for x :: "t"
  and y :: "t"
consts lt :: "t \<Rightarrow> t \<Rightarrow> bool"
axiomatization where lt_def:   "lt x y \<longleftrightarrow> le x y \<and> \<not>le y x"
  for x :: "t"
  and y :: "t"
axiomatization where Total:   "le x y \<or> le y x"
  for x :: "t"
  and y :: "t"
typedecl 'a t1
definition key :: "t \<times> 'a \<Rightarrow> t"
  where "key t2 = (case t2 of (a, _) \<Rightarrow> a)" for t2
theorem eq_def1:
  fixes x :: "t"
  fixes y :: "t"
  shows "eq x y \<longleftrightarrow> le x y \<and> le y x"
  sorry
end
