theory mpz_realloc2_Zrealloc2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/util_Util" "../../lib/isabelle/ptralias_Alias" "../../lib/isabelle/compare_Compare" "../../lib/isabelle/mpz_Z" "../../lib/isabelle/mpz_Zutil"
begin
definition alloc_of_bits :: "int \<Rightarrow> int"
  where "alloc_of_bits bits = (if bits \<le> (0 :: int) then 1 :: int else (bits + (63 :: int)) ediv (64 :: int))" for bits
end
