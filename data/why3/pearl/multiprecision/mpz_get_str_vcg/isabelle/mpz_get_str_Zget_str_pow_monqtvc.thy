theory mpz_get_str_Zget_str_pow_monqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "mach.c_String" "mach.c_UChar" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.mpz_Z" "pearl_multiprecision_lib.mpz_Zutil" "pearl_multiprecision_lib.base_info_BaseInfo" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_Logical" "pearl_multiprecision_lib.logical_LogicalOld" "pearl_multiprecision_lib.stringlemmas_String_lemmas" "pearl_multiprecision_lib.stringlemmas_Conversions" "pearl_multiprecision_lib.stringlemmas_String_value" "pearl_multiprecision_lib.get_str_Get_str" "pearl_multiprecision_lib.powm_Powm" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.valuation_Valuation" "pearl_multiprecision_lib.add_Add" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.mul_Mul" "pearl_multiprecision_lib.mul_Mul_basecase" "pearl_multiprecision_lib.div_Div" "pearl_multiprecision_lib.toom_Toom" "pearl_multiprecision_lib.add_1_Add_1" "pearl_multiprecision_lib.sub_1_Sub_1"
begin
definition effective :: "int \<Rightarrow> int"
  where "effective b = (if abs b < (2 :: int) then 10 :: int else abs b)" for b
theorem pow_mon'vc:
  fixes b :: "int"
  fixes x :: "int"
  fixes y :: "int"
  assumes fact0: "(1 :: int) < b"
  assumes fact1: "(0 :: int) \<le> x"
  assumes fact2: "(0 :: int) \<le> y"
  assumes fact3: "(0 :: int) \<le> b ^\<^sub>i x"
  assumes fact4: "b ^\<^sub>i x \<le> b ^\<^sub>i y"
  shows "x \<le> y"
  sorry
end
