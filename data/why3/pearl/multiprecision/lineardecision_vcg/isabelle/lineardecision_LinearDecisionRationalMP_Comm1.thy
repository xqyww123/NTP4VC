theory lineardecision_LinearDecisionRationalMP_Comm1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Comm:
  fixes x :: "real"
  fixes y :: "real"
  shows "x * y = y * x"
  sorry
end
