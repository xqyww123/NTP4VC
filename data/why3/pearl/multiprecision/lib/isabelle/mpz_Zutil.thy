theory mpz_Zutil
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mpz_Z" "mach.int_Unsigned" "mach.c_C" "types_Config" "types_Types" "types_Int32Eq" "types_UInt64Eq" "lemmas_Lemmas"
begin
typedecl  mpz_mem
consts ptr :: "mpz_mem \<Rightarrow> mpz_ptr"
consts ok :: "mpz_mem \<Rightarrow> bool"
end
