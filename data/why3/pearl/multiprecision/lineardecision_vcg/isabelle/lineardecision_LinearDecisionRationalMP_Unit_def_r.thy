theory lineardecision_LinearDecisionRationalMP_Unit_def_r
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Unit_def_r:
  fixes x :: "real"
  shows "x + (0 :: Real.real) = x"
  sorry
end
