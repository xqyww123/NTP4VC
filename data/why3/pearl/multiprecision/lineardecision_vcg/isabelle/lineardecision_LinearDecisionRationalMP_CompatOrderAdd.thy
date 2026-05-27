theory lineardecision_LinearDecisionRationalMP_CompatOrderAdd
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem CompatOrderAdd:
  fixes x :: "real"
  fixes y :: "real"
  fixes z :: "real"
  assumes fact0: "x \<le> y"
  shows "x + z \<le> y + z"
  sorry
end
