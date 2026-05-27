theory lineardecision_LinearDecisionRational_Mul_distr_l
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "pearl_multiprecision_lib.lineardecision_RationalCoeffs"
begin
theorem Mul_distr_l:
  fixes x :: "real"
  fixes y :: "real"
  fixes z :: "real"
  shows "x * (y + z) = x * y + x * z"
  sorry
end
