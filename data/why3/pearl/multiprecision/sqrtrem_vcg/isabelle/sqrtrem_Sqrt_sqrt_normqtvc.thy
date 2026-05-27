theory sqrtrem_Sqrt_sqrt_normqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "Why3STD.real_Truncate" "mach.c_C" "mach.int_Unsigned" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.add_1_Add_1" "pearl_multiprecision_lib.add_Add" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_1_Sub_1" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.mul_Mul" "pearl_multiprecision_lib.mul_Mul_basecase" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_Logical" "pearl_multiprecision_lib.logical_LogicalOld" "pearl_multiprecision_lib.div_Div" "pearl_multiprecision_lib.sqrt_Sqrt1" "mach.fxp_Fxp" "pearl_multiprecision_lib.toom_Toom" "pearl_multiprecision_lib.valuation_Valuation"
begin
definition ceilhalf :: "int \<Rightarrow> int"
  where "ceilhalf n = (n + (1 :: int)) cdiv (2 :: int)" for n
axiomatization where ceilhalf'spec'0:   "n \<le> (2 :: int) * ceilhalf n"
  for n :: "int"
axiomatization where ceilhalf'spec:   "n < (2 :: int) * (ceilhalf n + (1 :: int))"
  for n :: "int"
theorem sqrt_norm'vc:
  fixes c :: "int"
  fixes n :: "int"
  fixes s :: "int"
  fixes s0 :: "int"
  assumes fact0: "(0 :: int) \<le> c"
  assumes fact1: "(0 :: int) < n"
  assumes fact2: "(0 :: int) \<le> s"
  assumes fact3: "(0 :: int) \<le> s0"
  assumes fact4: "s0 < (2 :: int) ^\<^sub>i c"
  assumes fact5: "((2 :: int) ^\<^sub>i c * s + s0) * ((2 :: int) ^\<^sub>i c * s + s0) \<le> (2 :: int) ^\<^sub>i ((2 :: int) * c) * n"
  assumes fact6: "(2 :: int) ^\<^sub>i ((2 :: int) * c) * n < ((2 :: int) ^\<^sub>i c * s + s0 + (1 :: int)) * ((2 :: int) ^\<^sub>i c * s + s0 + (1 :: int))"
  shows "s * s \<le> n"
  and "n < (s + (1 :: int)) * (s + (1 :: int))"
  sorry
end
