theory kleene_algebra_RelAlgebra_postqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "Why3STD.map_MapExt"
begin
typedecl  a
typedecl  t
consts fc :: "a \<Rightarrow> a \<times> a"
axiomatization where fc_def:   "fc a1 = (a1, a1)"
  for a1 :: "a"
definition one :: "(a \<times> a) set"
  where "one = image fc UNIV"
consts o1 :: "a \<Rightarrow> a \<times> a \<Rightarrow> bool"
consts o2 :: "a \<Rightarrow> a \<times> a \<Rightarrow> bool"
consts o3 :: "a \<times> a \<Rightarrow> a"
axiomatization where o1_def:   "o1 x p = True \<longleftrightarrow> (case p of (a1, _) \<Rightarrow> a1 = x)"
  for x :: "a"
  and p :: "a \<times> a"
axiomatization where o2_def:   "o2 x p = True \<longleftrightarrow> (case p of (a1, _) \<Rightarrow> a1 = x)"
  for x :: "a"
  and p :: "a \<times> a"
axiomatization where o3_def:   "o3 p = (case p of (_, a2) \<Rightarrow> a2)"
  for p :: "a \<times> a"
theorem post'vc:
  fixes y :: "a"
  fixes s :: "(a \<times> a) set"
  fixes x :: "a"
  shows "y \<in> image o3 (set_filter s (o2 x)) \<longleftrightarrow> (x, y) \<in> s"
  sorry
end
