theory powm_Powm_valueb_monqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.valuation_Valuation" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.add_Add" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.mul_Mul" "pearl_multiprecision_lib.mul_Mul_basecase" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_Logical" "pearl_multiprecision_lib.logical_LogicalOld" "pearl_multiprecision_lib.div_Div" "pearl_multiprecision_lib.toom_Toom" "pearl_multiprecision_lib.add_1_Add_1" "pearl_multiprecision_lib.sub_1_Sub_1"
begin
definition redc :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "redc ur u n m \<longleftrightarrow> ur emod m = ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i n * u emod m" for ur u n m
definition valueb :: "64 word ptr \<Rightarrow> int \<Rightarrow> int"
  where "valueb p nbits = (if nbits < (0 :: int) then 0 :: int else let i :: int = nbits ediv (64 :: int) in value p i + ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i i * (uint (pelts p (offset p + i)) emod (2 :: int) ^\<^sub>i (nbits - (64 :: int) * i)))" for p nbits
theorem valueb_mon'vc:
  fixes bi1 :: "32 word"
  fixes bi2 :: "32 word"
  fixes p :: "64 word ptr"
  fixes pn :: "32 word"
  assumes fact0: "(0 :: int) \<le> sint bi1"
  assumes fact1: "sint bi1 \<le> sint bi2"
  assumes fact2: "valid p (sint pn)"
  assumes fact3: "(sint bi2 + (63 :: int)) ediv (64 :: int) \<le> sint pn"
  shows "valueb p (sint bi1) \<le> valueb p (sint bi2)"
  sorry
end
