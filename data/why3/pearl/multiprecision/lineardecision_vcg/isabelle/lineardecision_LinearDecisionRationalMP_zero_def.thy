theory lineardecision_LinearDecisionRationalMP_zero_def
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
axiomatization where sub_def:   "a1 - a2 = a1 + -a2"
  for a1 :: "real"
  and a2 :: "real"
typedecl  vars
theorem zero_def:
  fixes y :: "int \<Rightarrow> int"
  shows "minterp ((0 :: int, 1 :: int), Lit (0 :: int)) y = (0 :: Real.real)"
  sorry
end
