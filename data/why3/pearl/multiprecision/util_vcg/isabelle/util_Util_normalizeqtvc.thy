theory util_Util_normalizeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem normalize'vc:
  fixes n :: "32 word"
  fixes p :: "64 word ptr"
  assumes fact0: "(0 :: int) \<le> sint n"
  assumes fact1: "valid p (sint n)"
  shows "(0 :: int) \<le> sint n"
  and "sint n \<le> sint n"
  and "\<forall>(n1 :: 32 word). value p (sint n1) = value p (sint n) \<and> (0 :: int) \<le> sint n1 \<and> sint n1 \<le> sint n \<longrightarrow> (if (0 :: int) < sint n1 then int'32_in_bounds (sint n1 - (1 :: int)) \<and> (\<forall>(o1 :: 32 word). sint o1 = sint n1 - (1 :: int) \<longrightarrow> (c_C.min p \<le> offset p + sint o1 \<and> offset p + sint o1 < c_C.max p) \<and> (let o2 :: 64 word = pelts p (offset p + sint o1) in \<forall>(o3 :: bool). (uint o2 = uint (0 :: 64 word) \<longrightarrow> o3 = True) \<and> (o3 = True \<longrightarrow> o2 = (0 :: 64 word)) \<longrightarrow> (if \<not>o3 = True then ((0 :: int) \<le> sint n1 \<and> sint n1 \<le> sint n) \<and> value p (sint n1) = value p (sint n) \<and> (sint n1 = (0 :: int) \<or> (0 :: int) < uint (pelts p (offset p + sint n1 - (1 :: int)))) \<and> (sint n1 = (0 :: int) \<or> ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (sint n1 - (1 :: int)) \<le> value p (sint n1)) else int'32_in_bounds (sint n1 - (1 :: int)) \<and> (\<forall>(o4 :: 32 word). sint o4 = sint n1 - (1 :: int) \<longrightarrow> sint o4 < sint n1 \<and> value p (sint o4) = value p (sint n) \<and> (0 :: int) \<le> sint o4 \<and> sint o4 \<le> sint n)))) else ((0 :: int) \<le> sint n1 \<and> sint n1 \<le> sint n) \<and> value p (sint n1) = value p (sint n) \<and> (sint n1 = (0 :: int) \<or> (0 :: int) < uint (pelts p (offset p + sint n1 - (1 :: int)))) \<and> (sint n1 = (0 :: int) \<or> ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (sint n1 - (1 :: int)) \<le> value p (sint n1)))"
  sorry
end
