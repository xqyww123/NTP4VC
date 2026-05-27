theory div_Div_bounds_imply_rec3by2qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_LogicalOld"
begin
definition reciprocal :: "64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal v d \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv uint d - ((18446744073709551615 :: int) + (1 :: int))" for v d
definition reciprocal_3by2 :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal_3by2 v dh dl \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv (uint dl + ((18446744073709551615 :: int) + (1 :: int)) * uint dh) - ((18446744073709551615 :: int) + (1 :: int))" for v dh dl
theorem bounds_imply_rec3by2'vc:
  fixes dl :: "64 word"
  fixes dh :: "64 word"
  fixes v :: "64 word"
  assumes fact0: "((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (uint dl + ((18446744073709551615 :: int) + (1 :: int)) * uint dh) \<le> ((18446744073709551615 :: int) + (1 :: int) + uint v) * (uint dl + ((18446744073709551615 :: int) + (1 :: int)) * uint dh)"
  assumes fact1: "((18446744073709551615 :: int) + (1 :: int) + uint v) * (uint dl + ((18446744073709551615 :: int) + (1 :: int)) * uint dh) < ((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int))"
  shows "reciprocal_3by2 v dh dl"
  sorry
end
