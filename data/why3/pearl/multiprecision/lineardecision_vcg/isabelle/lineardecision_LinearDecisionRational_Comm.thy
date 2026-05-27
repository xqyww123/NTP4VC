theory lineardecision_LinearDecisionRational_Comm
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Comm:
  fixes x :: "real"
  fixes y :: "real"
  shows "x + y = y + x"
  sorry
end
