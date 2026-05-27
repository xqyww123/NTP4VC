theory lineardecision_LinearDecisionRational_sub_def
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem sub_def:
  fixes a1 :: "real"
  fixes a2 :: "real"
  shows "a1 - a2 = a1 + -a2"
  sorry
end
