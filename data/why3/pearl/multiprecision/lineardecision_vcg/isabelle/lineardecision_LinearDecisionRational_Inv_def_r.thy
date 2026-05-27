theory lineardecision_LinearDecisionRational_Inv_def_r
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Inv_def_r:
  fixes x :: "real"
  shows "x + -x = (0 :: Real.real)"
  sorry
end
