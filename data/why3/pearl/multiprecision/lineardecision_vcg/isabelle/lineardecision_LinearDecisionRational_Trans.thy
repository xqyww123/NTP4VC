theory lineardecision_LinearDecisionRational_Trans
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Trans:
  fixes x :: "real"
  fixes y :: "real"
  fixes z :: "real"
  assumes fact0: "x \<le> y"
  assumes fact1: "y \<le> z"
  shows "x \<le> z"
  sorry
end
