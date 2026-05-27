theory sqrt_Sqrt1_real_sqr_compatqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "Why3STD.real_Truncate" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "mach.fxp_Fxp"
begin
theorem real_sqr_compat'vc:
  fixes x :: "real"
  fixes y :: "real"
  assumes fact0: "(0 :: Real.real) < x"
  assumes fact1: "x < y"
  shows "x * x < y * y"
  sorry
end
