theory lineardecision_LinearDecisionRational_Antisymm
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Antisymm:
  fixes x :: "real"
  fixes y :: "real"
  assumes fact0: "x \<le> y"
  assumes fact1: "y \<le> x"
  shows "x = y"
  sorry
end
