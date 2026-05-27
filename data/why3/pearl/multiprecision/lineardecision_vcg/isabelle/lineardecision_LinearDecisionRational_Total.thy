theory lineardecision_LinearDecisionRational_Total
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Total:
  fixes x :: "real"
  fixes y :: "real"
  shows "x \<le> y \<or> y \<le> x"
  sorry
end
