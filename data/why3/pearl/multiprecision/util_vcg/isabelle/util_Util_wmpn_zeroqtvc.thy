theory util_Util_wmpn_zeroqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem wmpn_zero'vc:
  fixes r :: "64 word ptr"
  fixes sz :: "32 word"
  assumes fact0: "valid r (sint sz)"
  assumes fact1: "writable r = True"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> sint sz"
  and "value r (0 :: int) = (0 :: int)"
  and "\<forall>(i :: 32 word) (r1 :: 64 word ptr). length (data r1) = length (data r) \<and> offset r1 = offset r \<and> c_C.min r1 = c_C.min r \<and> c_C.max r1 = c_C.max r \<and> writable r1 = writable r \<and> zone1 r1 = zone1 r \<longrightarrow> ((0 :: int) \<le> sint i \<and> sint i \<le> sint sz) \<and> value r1 (sint i) = (0 :: int) \<and> (\<forall>(j :: int). j < offset r1 \<or> offset r1 + sint sz \<le> j \<longrightarrow> pelts r1 j = pelts r j) \<longrightarrow> (if sint i < sint sz then ((c_C.min r1 \<le> offset r1 + sint i \<and> offset r1 + sint i < c_C.max r1) \<and> writable r1 = True) \<and> (\<forall>(r2 :: 64 word ptr). length (data r2) = length (data r1) \<and> offset r2 = offset r1 \<and> c_C.min r2 = c_C.min r1 \<and> c_C.max r2 = c_C.max r1 \<and> writable r2 = writable r1 \<and> zone1 r2 = zone1 r1 \<longrightarrow> pelts r2 = (pelts r1)(offset r2 + sint i := 0 :: 64 word) \<and> pelts r2 (offset r2 + sint i) = (0 :: 64 word) \<longrightarrow> int'32_in_bounds (sint i + (1 :: int)) \<and> (\<forall>(o1 :: 32 word). sint o1 = sint i + (1 :: int) \<longrightarrow> ((0 :: int) \<le> sint sz - sint i \<and> sint sz - sint o1 < sint sz - sint i) \<and> ((0 :: int) \<le> sint o1 \<and> sint o1 \<le> sint sz) \<and> value r2 (sint o1) = (0 :: int) \<and> (\<forall>(j :: int). j < offset r2 \<or> offset r2 + sint sz \<le> j \<longrightarrow> pelts r2 j = pelts r j))) else value r1 (sint sz) = (0 :: int) \<and> (\<forall>(j :: int). j < offset r1 \<or> offset r1 + sint sz \<le> j \<longrightarrow> pelts r1 j = pelts r j))"
  sorry
end
