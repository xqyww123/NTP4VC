theory kleene_algebra_RelAlgebra_one_defqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "Why3STD.map_MapExt"
begin
typedecl  a
typedecl  t
consts fc :: "a \<Rightarrow> a \<times> a"
axiomatization where fc_def:   "fc a1 = (a1, a1)"
  for a1 :: "a"
definition one :: "(a \<times> a) set"
  where "one = image fc UNIV"
theorem one_def'vc:
  fixes x :: "a"
  shows "(x, x) \<in> one"
  sorry
end
