theory kleene_algebra_RelAlgebra_preqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "Why3STD.map_MapExt"
begin
typedecl  a
typedecl  t
consts fc :: "a \<Rightarrow> a \<times> a"
axiomatization where fc_def:   "fc a1 = (a1, a1)"
  for a1 :: "a"
definition one :: "(a \<times> a) set"
  where "one = image fc UNIV"
consts result :: "a \<times> a \<Rightarrow> a"
consts result1 :: "a \<Rightarrow> a \<times> a \<Rightarrow> bool"
axiomatization where result_def:   "result p = (case p of (_, a2) \<Rightarrow> a2)"
  for p :: "a \<times> a"
axiomatization where result1_def:   "result1 x p = True \<longleftrightarrow> (case p of (a1, _) \<Rightarrow> a1 = x)"
  for x :: "a"
  and p :: "a \<times> a"
definition post :: "(a \<times> a) set \<Rightarrow> a \<Rightarrow> a set"
  where "post s x = image result (set_filter s (result1 x))" for s x
axiomatization where post'spec:   "y \<in> post s x \<longleftrightarrow> (x, y) \<in> s"
  for y :: "a"
  and s :: "(a \<times> a) set"
  and x :: "a"
consts o1 :: "a \<Rightarrow> a \<times> a \<Rightarrow> bool"
consts o2 :: "a \<Rightarrow> a \<times> a \<Rightarrow> bool"
consts o3 :: "a \<times> a \<Rightarrow> a"
axiomatization where o1_def:   "o1 y p = True \<longleftrightarrow> (case p of (_, a2) \<Rightarrow> a2 = y)"
  for y :: "a"
  and p :: "a \<times> a"
axiomatization where o2_def:   "o2 y p = True \<longleftrightarrow> (case p of (_, a2) \<Rightarrow> a2 = y)"
  for y :: "a"
  and p :: "a \<times> a"
axiomatization where o3_def:   "o3 p = (case p of (a1, _) \<Rightarrow> a1)"
  for p :: "a \<times> a"
theorem pre'vc:
  fixes x :: "a"
  fixes s :: "(a \<times> a) set"
  fixes y :: "a"
  shows "x \<in> image o3 (set_filter s (o2 y)) \<longleftrightarrow> (x, y) \<in> s"
  sorry
end
