theory lineardecision_LinearDecisionRationalMP_Trans
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Trans:
  fixes x :: "real"
  fixes y :: "real"
  fixes z :: "real"
  assumes fact0: "x \<le> y"
  assumes fact1: "y \<le> z"
  shows "x \<le> z"
  sorry
end
