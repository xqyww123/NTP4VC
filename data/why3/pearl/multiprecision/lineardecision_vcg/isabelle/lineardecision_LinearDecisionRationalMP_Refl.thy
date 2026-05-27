theory lineardecision_LinearDecisionRationalMP_Refl
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Refl:
  fixes x :: "real"
  shows "x \<le> x"
  sorry
end
