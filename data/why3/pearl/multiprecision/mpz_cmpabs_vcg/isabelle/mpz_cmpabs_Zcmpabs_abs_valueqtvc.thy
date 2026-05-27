theory mpz_cmpabs_Zcmpabs_abs_valueqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.mpz_Z" "pearl_multiprecision_lib.mpz_Zutil"
begin
theorem abs_value'vc:
  fixes u :: "mpz_ptr"
  fixes mpz :: "mpz_memo"
  shows "abs (value_of u mpz) = abs_value_of mpz u"
  sorry
end
