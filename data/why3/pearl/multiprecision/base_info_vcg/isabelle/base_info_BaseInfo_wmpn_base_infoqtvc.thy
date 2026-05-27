theory base_info_BaseInfo_wmpn_base_infoqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "mach.c_C" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.logical_Logical" "pearl_multiprecision_lib.ptralias_Alias"
begin
theorem wmpn_base_info'vc:
  shows "(2 :: int) \<le> (2 :: int)"
  and "(2 :: int) \<le> (256 :: int)"
  and "(2 :: int) \<le> (2 :: int) \<and> (2 :: int) \<le> (256 :: int) \<longrightarrow> ((9223372036854775808 :: int) < (18446744073709551615 :: int) + (1 :: int) \<and> (18446744073709551615 :: int) + (1 :: int) \<le> (9223372036854775808 :: int) * (2 :: int)) \<and> ((9223372036854775808 :: int) < (18446744073709551615 :: int) + (1 :: int) \<and> (18446744073709551615 :: int) + (1 :: int) \<le> (9223372036854775808 :: int) * (2 :: int) \<longrightarrow> ((7 :: int) \<le> (63 :: int) \<and> (63 :: int) \<le> (63 :: int)) \<and> ((7 :: int) \<le> (63 :: int) \<and> (63 :: int) \<le> (63 :: int) \<longrightarrow> (9223372036854775808 :: int) = (2 :: int) ^\<^sub>i (63 :: int)))"
  sorry
end
