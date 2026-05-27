theory lineardecision_LinearDecisionRationalMP_Unitary
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Unitary:
  fixes x :: "real"
  shows "(1 :: Real.real) * x = x"
  sorry
end
