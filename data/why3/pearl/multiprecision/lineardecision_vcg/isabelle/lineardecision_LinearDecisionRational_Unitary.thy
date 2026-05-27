theory lineardecision_LinearDecisionRational_Unitary
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Unitary:
  fixes x :: "real"
  shows "(1 :: Real.real) * x = x"
  sorry
end
