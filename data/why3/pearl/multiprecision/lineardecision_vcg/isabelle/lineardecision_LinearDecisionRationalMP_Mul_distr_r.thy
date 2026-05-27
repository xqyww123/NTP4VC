theory lineardecision_LinearDecisionRationalMP_Mul_distr_r
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Mul_distr_r:
  fixes y :: "real"
  fixes z :: "real"
  fixes x :: "real"
  shows "(y + z) * x = y * x + z * x"
  sorry
end
