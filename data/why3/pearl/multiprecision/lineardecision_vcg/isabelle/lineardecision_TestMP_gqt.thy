theory lineardecision_TestMP_gqt
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "mach.matrix_Matrix63" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs" "pearl_multiprecision_lib.lineardecision_LinearDecisionRationalMP" "pearl_multiprecision_lib.lineardecision_LinearDecisionIntMP" "pearl_multiprecision_lib.lineardecision_EqPropMP"
begin
theorem g':
  fixes i :: "int"
  fixes a :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "(0 :: int) \<le> i + (1 :: int)"
  shows "((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (i + (1 :: int)) * a = ((18446744073709551615 :: int) + (1 :: int)) * (((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i i * a)"
  sorry
end
