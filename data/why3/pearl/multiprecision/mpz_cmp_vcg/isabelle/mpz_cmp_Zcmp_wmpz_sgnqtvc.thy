theory mpz_cmp_Zcmp_wmpz_sgnqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.mpz_Z" "pearl_multiprecision_lib.mpz_Zutil" "pearl_multiprecision_lib.mpz_getset_Set"
begin
theorem wmpz_sgn'vc:
  fixes mpz :: "mpz_memo"
  fixes u :: "mpz_ptr"
  assumes fact0: "(0 :: int) \<le> readers mpz u"
  shows "-(2 :: int) < readers mpz u"
  and "\<forall>(o1 :: 32 word). sint o1 = sgn mpz u * abs_size mpz u \<longrightarrow> (\<not>sint o1 < (0 :: int) \<longrightarrow> -(2 :: int) < readers mpz u) \<and> (\<forall>(result :: 32 word). (if sint o1 < (0 :: int) then result = Groups.uminus_class.uminus (1 :: 32 word) else \<exists>(o2 :: 32 word). sint o2 = sgn mpz u * abs_size mpz u \<and> (if (0 :: int) < sint o2 then result = (1 :: 32 word) else result = (0 :: 32 word))) \<longrightarrow> (\<forall>(w :: mpz_ptr). mpz_unchanged w mpz mpz) \<and> ((0 :: int) < sint result \<longrightarrow> (0 :: int) < value_of u mpz) \<and> (sint result < (0 :: int) \<longrightarrow> value_of u mpz < (0 :: int)) \<and> (sint result = (0 :: int) \<longrightarrow> value_of u mpz = (0 :: int)))"
  sorry
end
