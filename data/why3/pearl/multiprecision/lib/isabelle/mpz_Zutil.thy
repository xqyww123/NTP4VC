theory mpz_Zutil
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "../../lib/isabelle/mpz_Z" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas"
begin
typedecl  mpz_mem
consts ptr :: "mpz_mem \<Rightarrow> mpz_ptr"
consts ok :: "mpz_mem \<Rightarrow> bool"
end
