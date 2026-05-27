theory logical_LogicalUtil_clz_extqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem clz_ext'vc:
  fixes x :: "64 word"
  assumes fact0: "(0 :: int) < uint x"
  shows "(0 :: int) < uint x"
  and "\<forall>(r :: 32 word). (2 :: int) ^\<^sub>i sint r * uint x \<le> (18446744073709551615 :: int) \<and> (18446744073709551615 :: int) < (2 :: int) * (2 :: int) ^\<^sub>i sint r * uint x \<and> (0 :: int) \<le> sint r \<and> sint r < (64 :: int) \<longrightarrow> (2 :: int) ^\<^sub>i sint r * uint x < (18446744073709551615 :: int) + (1 :: int) \<and> (18446744073709551615 :: int) + (1 :: int) \<le> (2 :: int) * (2 :: int) ^\<^sub>i sint r * uint x \<and> ((0 :: int) \<le> sint r \<and> sint r < (64 :: int)) \<and> (2 :: int) ^\<^sub>i sint r * uint x \<le> (18446744073709551615 :: int) + (1 :: int) - (2 :: int) ^\<^sub>i sint r"
  sorry
end
