theory kleene_algebra_RelAlgebra_infix_plqtvc
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
consts result2 :: "a \<times> a \<Rightarrow> a"
consts result3 :: "a \<Rightarrow> a \<times> a \<Rightarrow> bool"
axiomatization where result2_def:   "result2 p = (case p of (a1, _) \<Rightarrow> a1)"
  for p :: "a \<times> a"
axiomatization where result3_def:   "result3 y p = True \<longleftrightarrow> (case p of (_, a2) \<Rightarrow> a2 = y)"
  for y :: "a"
  and p :: "a \<times> a"
definition pre :: "(a \<times> a) set \<Rightarrow> a \<Rightarrow> a set"
  where "pre s y = image result2 (set_filter s (result3 y))" for s y
axiomatization where pre'spec:   "x \<in> pre s y \<longleftrightarrow> (x, y) \<in> s"
  for x :: "a"
  and s :: "(a \<times> a) set"
  and y :: "a"
theorem infix_pl'vc:
  fixes x :: "a \<times> a"
  fixes s1 :: "(a \<times> a) set"
  fixes s2 :: "(a \<times> a) set"
  shows "x \<in> s1 \<union> s2 \<longleftrightarrow> x \<in> s1 \<or> x \<in> s2"
  sorry
end
