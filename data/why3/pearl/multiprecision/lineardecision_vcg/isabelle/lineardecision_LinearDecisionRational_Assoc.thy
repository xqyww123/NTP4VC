theory lineardecision_LinearDecisionRational_Assoc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Assoc:
  fixes x :: "real"
  fixes y :: "real"
  fixes z :: "real"
  shows "x + y + z = x + (y + z)"
  sorry
end
