theory toom_Toom_no_borrowqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "pearl_multiprecision_lib.valuation_Valuation" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.add_1_Add_1" "pearl_multiprecision_lib.add_Add" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_1_Sub_1" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.mul_Mul" "pearl_multiprecision_lib.mul_Mul_basecase" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_Logical"
begin
theorem no_borrow'vc:
  fixes y :: "int"
  fixes x :: "int"
  fixes r :: "int"
  fixes m :: "int"
  fixes b :: "int"
  assumes fact0: "(0 :: int) \<le> y"
  assumes fact1: "y \<le> x"
  assumes fact2: "(0 :: int) \<le> r"
  assumes fact3: "r < m"
  assumes fact4: "r - m * b = x - y"
  assumes fact5: "(0 :: int) \<le> b"
  shows "b = (0 :: int)"
  sorry
end
