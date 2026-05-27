theory lineardecision_LinearDecisionRational_NonTrivialRing
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem NonTrivialRing:
  shows "\<not>(0 :: Real.real) = (1 :: Real.real)"
  sorry
end
