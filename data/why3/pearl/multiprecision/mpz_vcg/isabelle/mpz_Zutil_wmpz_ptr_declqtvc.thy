theory mpz_Zutil_wmpz_ptr_declqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "pearl_multiprecision_lib.mpz_Z" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
typedecl  mpz_mem
consts ptr :: "mpz_mem \<Rightarrow> mpz_ptr"
consts ok :: "mpz_mem \<Rightarrow> bool"
theorem wmpz_ptr_decl'vc:
  fixes mpz :: "mpz_memo"
  fixes t :: "mpz_ptr"
  fixes mpz1 :: "mpz_memo"
  fixes memo :: "mpz_mem"
  assumes fact0: "readers mpz t = -(2 :: int)"
  assumes fact1: "\<forall>(x :: mpz_ptr). \<not>x = t \<longrightarrow> mpz_unchanged x mpz1 mpz"
  assumes fact2: "readers mpz1 t = (0 :: int)"
  assumes fact3: "alloc mpz1 t = (0 :: int)"
  assumes fact4: "abs_size mpz1 t = (0 :: int)"
  assumes fact5: "ptr memo = t"
  assumes fact6: "ok memo = True"
  shows "t = ptr memo"
  and "ok memo = True"
  and "readers mpz1 t = (0 :: int)"
  and "alloc mpz1 t = (0 :: int)"
  and "abs_size mpz1 t = (0 :: int)"
  and "readers mpz t = -(2 :: int)"
  and "\<forall>(x :: mpz_ptr). \<not>x = t \<longrightarrow> mpz_unchanged x mpz1 mpz"
  sorry
end
