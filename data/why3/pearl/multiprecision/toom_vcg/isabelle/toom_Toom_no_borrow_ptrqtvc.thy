theory toom_Toom_no_borrow_ptrqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "pearl_multiprecision_lib.valuation_Valuation" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.add_1_Add_1" "pearl_multiprecision_lib.add_Add" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_1_Sub_1" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.mul_Mul" "pearl_multiprecision_lib.mul_Mul_basecase" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_Logical"
begin
theorem no_borrow_ptr'vc:
  fixes ny :: "int"
  fixes nx :: "int"
  fixes y :: "64 word ptr"
  fixes x :: "64 word ptr"
  fixes r :: "64 word ptr"
  fixes b :: "64 word"
  assumes fact0: "(0 :: int) < ny"
  assumes fact1: "ny \<le> nx"
  assumes fact2: "value y ny \<le> value x nx"
  assumes fact3: "value r nx - ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i nx * uint b = value x nx - value y ny"
  assumes fact4: "(0 :: int) \<le> uint b"
  shows "uint b = (0 :: int)"
  sorry
end
