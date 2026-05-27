theory powm_Powm
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "types_Config" "types_Types" "types_Int32Eq" "types_UInt64Eq" "lemmas_Lemmas" "compare_Compare" "valuation_Valuation" "util_Util" "ptralias_Alias" "util_UtilOld" "add_Add" "add_AddOld" "sub_SubOld" "mul_Mul" "mul_Mul_basecase" "logical_LogicalUtil" "logical_Logical" "logical_LogicalOld" "div_Div" "toom_Toom" "add_1_Add_1" "sub_1_Sub_1"
begin
definition redc :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "redc ur u n m \<longleftrightarrow> ur emod m = ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i n * u emod m" for ur u n m
definition valueb :: "64 word ptr \<Rightarrow> int \<Rightarrow> int"
  where "valueb p nbits = (if nbits < (0 :: int) then 0 :: int else let i :: int = nbits ediv (64 :: int) in value p i + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i i * (uint (pelts p (offset p + i)) emod (2 :: int) ^\<^sub>i (nbits - (64 :: int) * i)))" for p nbits
end
