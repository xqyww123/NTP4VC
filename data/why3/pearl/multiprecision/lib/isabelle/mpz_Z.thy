theory mpz_Z
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas"
begin
typedecl  mpz_ptr
consts mpz_eq :: "mpz_ptr \<Rightarrow> mpz_ptr \<Rightarrow> bool"
axiomatization where mpz_eq'spec:   "mpz_eq x y \<longleftrightarrow> x = y"
  for x :: "mpz_ptr"
  and y :: "mpz_ptr"
typedecl  mpz_memo
consts abs_value_of :: "mpz_memo \<Rightarrow> mpz_ptr \<Rightarrow> int"
consts alloc :: "mpz_memo \<Rightarrow> mpz_ptr \<Rightarrow> int"
consts abs_size :: "mpz_memo \<Rightarrow> mpz_ptr \<Rightarrow> int"
consts sgn :: "mpz_memo \<Rightarrow> mpz_ptr \<Rightarrow> int"
consts readers :: "mpz_memo \<Rightarrow> mpz_ptr \<Rightarrow> int"
consts zones :: "mpz_memo \<Rightarrow> mpz_ptr \<Rightarrow> zone"
axiomatization where mpz_memo'invariant'0:   "(0 :: int) \<le> alloc self p"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
axiomatization where mpz_memo'invariant'1:   "sgn self p = (1 :: int) \<or> sgn self p = -(1 :: int)"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
axiomatization where mpz_memo'invariant'2:   "abs_size self p \<le> alloc self p"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
axiomatization where mpz_memo'invariant'3:   "(0 :: int) \<le> abs_size self p"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
axiomatization where mpz_memo'invariant'4:   "abs_size self p \<le> (2147483647 :: int)"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
axiomatization where mpz_memo'invariant'5:   "(0 :: int) \<le> abs_value_of self p"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
axiomatization where mpz_memo'invariant'6:   "(1 :: int) \<le> abs_size self p \<longrightarrow> ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i (abs_size self p - (1 :: int)) \<le> abs_value_of self p"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
axiomatization where mpz_memo'invariant'7:   "abs_value_of self p < ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i abs_size self p"
  for self :: "mpz_memo"
  and p :: "mpz_ptr"
definition value_of :: "mpz_ptr \<Rightarrow> mpz_memo \<Rightarrow> int"
  where "value_of x memo = sgn memo x * abs_value_of memo x" for x memo
definition sgn_value :: "64 word ptr \<Rightarrow> 32 word \<Rightarrow> int"
  where "sgn_value p sz = (if (0 :: int) \<le> sint sz then value p (sint sz) else -value p (-sint sz))" for p sz
definition mpz_unchanged :: "mpz_ptr \<Rightarrow> mpz_memo \<Rightarrow> mpz_memo \<Rightarrow> _"
  where "mpz_unchanged x memo1 memo2 \<longleftrightarrow> readers memo1 x = readers memo2 x \<and> (-(2 :: int) < readers memo1 x \<longrightarrow> abs_value_of memo1 x = abs_value_of memo2 x \<and> alloc memo1 x = alloc memo2 x \<and> abs_size memo1 x = abs_size memo2 x \<and> sgn memo1 x = sgn memo2 x \<and> zones memo1 x = zones memo2 x)" for x memo1 memo2
datatype  mpz_struct = mpz_struct'mk (addr: "mpz_ptr")
end
