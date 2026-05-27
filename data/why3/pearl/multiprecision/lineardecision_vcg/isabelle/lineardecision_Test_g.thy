theory lineardecision_Test_g
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "mach.matrix_Matrix63" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_LinearDecisionRational"
begin
theorem g:
  fixes x :: "real"
  fixes y :: "real"
  assumes fact0: "real_of_int (3 :: int) / real_of_int (1 :: int) * x + real_of_int (2 :: int) / real_of_int (1 :: int) * y = real_of_int (21 :: int) / real_of_int (1 :: int)"
  assumes fact1: "real_of_int (7 :: int) / real_of_int (1 :: int) * x + real_of_int (4 :: int) / real_of_int (1 :: int) * y = real_of_int (47 :: int) / real_of_int (1 :: int)"
  shows "x = real_of_int (5 :: int) / real_of_int (1 :: int)"
  sorry
end
