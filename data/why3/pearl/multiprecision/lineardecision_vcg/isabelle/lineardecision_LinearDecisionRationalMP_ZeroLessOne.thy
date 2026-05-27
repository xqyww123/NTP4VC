theory lineardecision_LinearDecisionRationalMP_ZeroLessOne
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs"
begin
typedecl  coeff
theorem ZeroLessOne:
  shows "(0 :: Real.real) \<le> (1 :: Real.real)"
  sorry
end
