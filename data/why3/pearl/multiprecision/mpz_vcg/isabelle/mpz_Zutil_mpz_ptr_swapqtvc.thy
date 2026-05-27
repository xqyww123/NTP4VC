theory mpz_Zutil_mpz_ptr_swapqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "pearl_multiprecision_lib.mpz_Z" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
typedecl  mpz_mem
consts ptr :: "mpz_mem \<Rightarrow> mpz_ptr"
consts ok :: "mpz_mem \<Rightarrow> bool"
theorem mpz_ptr_swap'vc:
  fixes mpz :: "mpz_memo"
  fixes x :: "mpz_ptr"
  fixes y :: "mpz_ptr"
  assumes fact0: "readers mpz x = (0 :: int)"
  assumes fact1: "readers mpz y = (0 :: int)"
  shows "readers mpz y = (0 :: int)"
  and "readers mpz x = (0 :: int)"
  sorry
end
