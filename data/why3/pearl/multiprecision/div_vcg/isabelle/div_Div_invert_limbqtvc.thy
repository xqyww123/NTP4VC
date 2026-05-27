theory div_Div_invert_limbqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_LogicalOld"
begin
definition reciprocal :: "64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal v d \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv uint d - ((18446744073709551615 :: int) + (1 :: int))" for v d
theorem invert_limb'vc:
  fixes d :: "64 word"
  assumes fact0: "((18446744073709551615 :: int) + (1 :: int)) ediv (2 :: int) \<le> uint d"
  shows "let o1 :: 64 word = uint'64_max in uint'64_in_bounds (uint o1 - uint d) \<and> (\<forall>(o2 :: 64 word). uint o2 = uint o1 - uint d \<longrightarrow> uint o2 < uint d \<and> (\<forall>(v :: 64 word). uint v = (uint uint'64_max + ((18446744073709551615 :: int) + (1 :: int)) * uint o2) ediv uint d \<longrightarrow> reciprocal v d))"
  sorry
end
