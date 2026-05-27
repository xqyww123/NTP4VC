theory sqrtrem_Sqrt
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "Why3STD.real_Truncate" "mach.c_C" "mach.int_Unsigned" "types_Config" "types_Types" "types_Int32Eq" "types_UInt64Eq" "lemmas_Lemmas" "compare_Compare" "util_Util" "ptralias_Alias" "util_UtilOld" "add_1_Add_1" "add_Add" "add_AddOld" "sub_1_Sub_1" "sub_SubOld" "mul_Mul" "mul_Mul_basecase" "logical_LogicalUtil" "logical_Logical" "logical_LogicalOld" "div_Div" "sqrt_Sqrt1" "mach.fxp_Fxp" "toom_Toom" "valuation_Valuation"
begin
definition ceilhalf :: "int \<Rightarrow> int"
  where "ceilhalf n = (n + (1 :: int)) cdiv (2 :: int)" for n
axiomatization where ceilhalf'spec'0:   "n \<le> (2 :: int) * ceilhalf n"
  for n :: "int"
axiomatization where ceilhalf'spec:   "n < (2 :: int) * (ceilhalf n + (1 :: int))"
  for n :: "int"
end
