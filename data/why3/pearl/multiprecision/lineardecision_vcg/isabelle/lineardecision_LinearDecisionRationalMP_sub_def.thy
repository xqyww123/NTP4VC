theory lineardecision_LinearDecisionRationalMP_sub_def
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem sub_def:
  fixes a1 :: "real"
  fixes a2 :: "real"
  shows "a1 - a2 = a1 + -a2"
  sorry
end
