theory lineardecision_LinearDecisionRational_Refl
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Refl:
  fixes x :: "real"
  shows "x \<le> x"
  sorry
end
