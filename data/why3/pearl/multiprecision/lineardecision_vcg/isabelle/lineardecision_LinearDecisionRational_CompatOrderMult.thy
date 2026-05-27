theory lineardecision_LinearDecisionRational_CompatOrderMult
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem CompatOrderMult:
  fixes x :: "real"
  fixes y :: "real"
  fixes z :: "real"
  assumes fact0: "x \<le> y"
  assumes fact1: "(0 :: Real.real) \<le> z"
  shows "x * z \<le> y * z"
  sorry
end
