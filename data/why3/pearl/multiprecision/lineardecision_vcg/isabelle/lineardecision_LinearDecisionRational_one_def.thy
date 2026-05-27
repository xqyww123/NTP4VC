theory lineardecision_LinearDecisionRational_one_def
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
axiomatization where sub_def:   "a1 - a2 = a1 + -a2"
  for a1 :: "real"
  and a2 :: "real"
typedecl  vars
axiomatization where zero_def:   "rinterp (0 :: int, 1 :: int) y = (0 :: Real.real)"
  for y :: "int \<Rightarrow> real"
theorem one_def:
  fixes y :: "int \<Rightarrow> real"
  shows "rinterp (1 :: int, 1 :: int) y = (1 :: Real.real)"
  sorry
end
