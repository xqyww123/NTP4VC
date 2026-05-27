theory lineardecision_LinearDecisionRational_invqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
axiomatization where sub_def:   "a1 - a2 = a1 + -a2"
  for a1 :: "real"
  and a2 :: "real"
typedecl  vars
axiomatization where zero_def:   "rinterp (0 :: int, 1 :: int) y = (0 :: Real.real)"
  for y :: "int \<Rightarrow> real"
axiomatization where one_def:   "rinterp (1 :: int, 1 :: int) y = (1 :: Real.real)"
  for y :: "int \<Rightarrow> real"
theorem inv'refn'vc:
  fixes a :: "int"
  fixes a1 :: "int"
  shows "let a2 :: int \<times> int = (a, a1) in \<not>req a2 (0 :: int, 1 :: int) \<longrightarrow> \<not>req a2 (0 :: int, 1 :: int) \<and> (\<forall>(result :: int) (result1 :: int). let result2 :: int \<times> int = (result, result1) in \<not>req result2 (0 :: int, 1 :: int) \<and> (\<forall>(y :: int \<Rightarrow> real). rinterp result2 y * rinterp a2 y = (1 :: Real.real)) \<longrightarrow> \<not>req result2 (0 :: int, 1 :: int))"
  sorry
end
