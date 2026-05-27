theory lineardecision_LinearDecisionRationalMP_Inv_def_l
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Inv_def_l:
  fixes x :: "real"
  shows "-x + x = (0 :: Real.real)"
  sorry
end
