theory mpz_Z_mpz_memoqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
typedecl  mpz_ptr
consts mpz_eq :: "mpz_ptr \<Rightarrow> mpz_ptr \<Rightarrow> bool"
axiomatization where mpz_eq'spec:   "mpz_eq x y \<longleftrightarrow> x = y"
  for x :: "mpz_ptr"
  and y :: "mpz_ptr"
consts o1 :: "mpz_ptr \<Rightarrow> int"
consts o2 :: "mpz_ptr \<Rightarrow> int"
consts o3 :: "mpz_ptr \<Rightarrow> int"
consts o4 :: "mpz_ptr \<Rightarrow> int"
axiomatization where o'def:   "o1 x = (1 :: int)"
  for x :: "mpz_ptr"
axiomatization where o'def1:   "o2 x = (0 :: int)"
  for x :: "mpz_ptr"
axiomatization where o'def2:   "o3 x = (0 :: int)"
  for x :: "mpz_ptr"
axiomatization where o'def3:   "o4 x = (0 :: int)"
  for x :: "mpz_ptr"
theorem mpz_memo'vc:
  shows "let o5 :: mpz_ptr \<Rightarrow> int = o1; o6 :: mpz_ptr \<Rightarrow> int = o2; o7 :: mpz_ptr \<Rightarrow> int = o3; o8 :: mpz_ptr \<Rightarrow> int = o4 in \<forall>(p :: mpz_ptr). (0 :: int) \<le> o7 p \<and> (o5 p = (1 :: int) \<or> o5 p = -(1 :: int)) \<and> o6 p \<le> o7 p \<and> ((0 :: int) \<le> o6 p \<and> o6 p \<le> (2147483647 :: int)) \<and> (0 :: int) \<le> o8 p \<and> ((1 :: int) \<le> o6 p \<longrightarrow> ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (o6 p - (1 :: int)) \<le> o8 p) \<and> o8 p < ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i o6 p"
  sorry
end
