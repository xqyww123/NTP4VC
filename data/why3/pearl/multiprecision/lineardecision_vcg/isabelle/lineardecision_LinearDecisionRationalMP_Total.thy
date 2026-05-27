theory lineardecision_LinearDecisionRationalMP_Total
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Total:
  fixes x :: "real"
  fixes y :: "real"
  shows "x \<le> y \<or> y \<le> x"
  sorry
end
