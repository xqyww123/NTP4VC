theory mpz_getset_Set_abs_castqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "pearl_multiprecision_lib.lemmas_Lemmas" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.mpz_Z" "pearl_multiprecision_lib.mpz_Zutil"
begin
theorem abs_cast'vc:
  fixes x :: "64 word"
  shows "if (0 :: int) \<le> sint x then (0 :: int) \<le> sint x else int'64_in_bounds (sint x + (1 :: int)) \<and> (\<forall>(o1 :: 64 word). sint o1 = sint x + (1 :: int) \<longrightarrow> int'64_in_bounds (-sint o1) \<and> (\<forall>(o2 :: 64 word). sint o2 = -sint o1 \<longrightarrow> (0 :: int) \<le> sint o2 \<and> (\<forall>(o3 :: 64 word). uint o3 = sint o2 \<longrightarrow> uint'64_in_bounds (uint o3 + (1 :: int)))))"
  and "\<forall>(result :: 64 word). (if (0 :: int) \<le> sint x then uint result = sint x else \<exists>(o1 :: 64 word). sint o1 = sint x + (1 :: int) \<and> (\<exists>(o2 :: 64 word). sint o2 = -sint o1 \<and> (\<exists>(o3 :: 64 word). uint o3 = sint o2 \<and> uint result = uint o3 + (1 :: int)))) \<longrightarrow> uint result = abs (sint x)"
  sorry
end
