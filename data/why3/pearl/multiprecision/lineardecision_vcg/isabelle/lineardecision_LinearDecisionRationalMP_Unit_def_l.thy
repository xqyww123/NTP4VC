theory lineardecision_LinearDecisionRationalMP_Unit_def_l
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem Unit_def_l:
  fixes x :: "real"
  shows "(0 :: Real.real) + x = x"
  sorry
end
