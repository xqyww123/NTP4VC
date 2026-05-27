theory lineardecision_TestInt_g
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "mach.matrix_Matrix63" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_LinearDecisionRational" "pearl_multiprecision_lib.lineardecision_LinearDecisionInt"
begin
theorem g:
  fixes x :: "int"
  fixes y :: "int"
  assumes fact0: "(3 :: int) * x + (2 :: int) * y = (21 :: int)"
  assumes fact1: "(7 :: int) * x + (4 :: int) * y = (47 :: int)"
  shows "x = (5 :: int)"
  sorry
end
