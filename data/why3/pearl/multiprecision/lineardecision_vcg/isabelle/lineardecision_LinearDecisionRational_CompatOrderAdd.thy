theory lineardecision_LinearDecisionRational_CompatOrderAdd
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem CompatOrderAdd:
  fixes x :: "real"
  fixes y :: "real"
  fixes z :: "real"
  assumes fact0: "x \<le> y"
  shows "x + z \<le> y + z"
  sorry
end
