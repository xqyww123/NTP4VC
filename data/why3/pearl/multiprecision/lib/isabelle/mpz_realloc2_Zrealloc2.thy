theory mpz_realloc2_Zrealloc2
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "lemmas_Lemmas" "types_Config" "types_Types" "types_Int32Eq" "types_UInt64Eq" "util_Util" "ptralias_Alias" "compare_Compare" "mpz_Z" "mpz_Zutil"
begin
definition alloc_of_bits :: "int \<Rightarrow> int"
  where "alloc_of_bits bits = (if bits \<le> (0 :: int) then 1 :: int else (bits + (63 :: int)) ediv (64 :: int))" for bits
end
