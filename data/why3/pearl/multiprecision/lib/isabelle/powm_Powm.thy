theory powm_Powm
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/compare_Compare" "../../lib/isabelle/valuation_Valuation" "../../lib/isabelle/util_Util" "../../lib/isabelle/ptralias_Alias" "../../lib/isabelle/util_UtilOld" "../../lib/isabelle/add_Add" "../../lib/isabelle/add_AddOld" "../../lib/isabelle/sub_SubOld" "../../lib/isabelle/mul_Mul" "../../lib/isabelle/mul_Mul_basecase" "../../lib/isabelle/logical_LogicalUtil" "../../lib/isabelle/logical_Logical" "../../lib/isabelle/logical_LogicalOld" "../../lib/isabelle/div_Div" "../../lib/isabelle/toom_Toom" "../../lib/isabelle/add_1_Add_1" "../../lib/isabelle/sub_1_Sub_1"
begin
definition redc :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "redc ur u n m \<longleftrightarrow> ur emod m = ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i n * u emod m" for ur u n m
definition valueb :: "64 word ptr \<Rightarrow> int \<Rightarrow> int"
  where "valueb p nbits = (if nbits < (0 :: int) then 0 :: int else let i :: int = nbits ediv (64 :: int) in value p i + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i i * (uint (pelts p (offset p + i)) emod (2 :: int) ^\<^sub>i (nbits - (64 :: int) * i)))" for p nbits
end
