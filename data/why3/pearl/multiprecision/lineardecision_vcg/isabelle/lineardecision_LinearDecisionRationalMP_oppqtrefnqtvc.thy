theory lineardecision_LinearDecisionRationalMP_oppqtrefnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
axiomatization where sub_def:   "a1 - a2 = a1 + -a2"
  for a1 :: "real"
  and a2 :: "real"
typedecl  vars
axiomatization where zero_def:   "minterp ((0 :: int, 1 :: int), Lit (0 :: int)) y = (0 :: Real.real)"
  for y :: "int \<Rightarrow> int"
axiomatization where one_def:   "minterp ((1 :: int, 1 :: int), Lit (0 :: int)) y = (1 :: Real.real)"
  for y :: "int \<Rightarrow> int"
theorem opp'refn'vc:
  shows "True"
  sorry
end
