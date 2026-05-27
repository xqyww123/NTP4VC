theory mpz_div2exp_Zdiv2exp_div_minusqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_Logical" "pearl_multiprecision_lib.logical_LogicalOld" "pearl_multiprecision_lib.mpz_Z" "pearl_multiprecision_lib.mpz_Zutil"
begin
theorem div_minus'vc:
  fixes y :: "int"
  fixes x :: "int"
  assumes fact0: "(0 :: int) < y"
  assumes fact1: "(0 :: int) \<le> x"
  shows "-x cdiv y = -(x cdiv y)"
  sorry
end
