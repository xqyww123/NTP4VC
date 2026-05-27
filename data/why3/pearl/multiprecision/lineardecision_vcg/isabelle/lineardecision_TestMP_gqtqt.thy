theory lineardecision_TestMP_gqtqt
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "mach.matrix_Matrix63" "Why3STD.debug_Debug" "pearl_multiprecision_lib.lineardecision_RationalCoeffs" "pearl_multiprecision_lib.lineardecision_MP64Coeffs" "pearl_multiprecision_lib.lineardecision_LinearDecisionRationalMP" "pearl_multiprecision_lib.lineardecision_LinearDecisionIntMP" "pearl_multiprecision_lib.lineardecision_EqPropMP"
begin
theorem g'':
  fixes i :: "int"
  fixes r :: "int"
  fixes x :: "int"
  fixes y :: "int"
  fixes l :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "r + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i i * (0 :: int) = x + y"
  shows "r + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i i * l + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (i + (1 :: int)) * (0 :: int) = x + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i i * l + y"
  sorry
end
