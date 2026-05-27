theory lineardecision_LinearDecisionRational_Mul_distr_r
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Mul_distr_r:
  fixes y :: "real"
  fixes z :: "real"
  fixes x :: "real"
  shows "(y + z) * x = y * x + z * x"
  sorry
end
