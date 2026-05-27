theory util_Util_wmpn_zero_pqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem wmpn_zero_p'vc:
  fixes x :: "64 word ptr"
  fixes sz :: "32 word"
  assumes fact0: "valid x (sint sz)"
  shows "(0 :: int) \<le> sint sz"
  and "sint sz \<le> sint sz"
  and "value_sub (pelts x) (offset x + sint sz) (offset x + sint sz) = (0 :: int)"
  and "\<forall>(i :: 32 word). ((0 :: int) \<le> sint i \<and> sint i \<le> sint sz) \<and> value_sub (pelts x) (offset x + sint i) (offset x + sint sz) = (0 :: int) \<longrightarrow> (if (1 :: int) \<le> sint i then int'32_in_bounds (sint i - (1 :: int)) \<and> (\<forall>(o1 :: 32 word). sint o1 = sint i - (1 :: int) \<longrightarrow> (c_C.min x \<le> offset x + sint o1 \<and> offset x + sint o1 < c_C.max x) \<and> ((uint (pelts x (offset x + sint o1)) = (0 :: int) \<longrightarrow> pelts x (offset x + sint o1) = (0 :: 64 word)) \<longrightarrow> (if \<not>pelts x (offset x + sint o1) = (0 :: 64 word) then ((0 :: int) \<le> sint (0 :: 32 word) \<and> sint (0 :: 32 word) \<le> (1 :: int)) \<and> (sint (0 :: 32 word) = (1 :: int) \<longleftrightarrow> value x (sint sz) = (0 :: int)) else ((0 :: int) \<le> sint i \<and> sint o1 < sint i) \<and> ((0 :: int) \<le> sint o1 \<and> sint o1 \<le> sint sz) \<and> value_sub (pelts x) (offset x + sint o1) (offset x + sint sz) = (0 :: int)))) else ((0 :: int) \<le> sint (1 :: 32 word) \<and> sint (1 :: 32 word) \<le> (1 :: int)) \<and> (sint (1 :: 32 word) = (1 :: int) \<longleftrightarrow> value x (sint sz) = (0 :: int)))"
  sorry
end
