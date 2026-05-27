theory powm_Powm_win_sizeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.c_C" "mach.int_Unsigned" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.compare_Compare" "pearl_multiprecision_lib.valuation_Valuation" "pearl_multiprecision_lib.util_Util" "pearl_multiprecision_lib.ptralias_Alias" "pearl_multiprecision_lib.util_UtilOld" "pearl_multiprecision_lib.add_Add" "pearl_multiprecision_lib.add_AddOld" "pearl_multiprecision_lib.sub_SubOld" "pearl_multiprecision_lib.mul_Mul" "pearl_multiprecision_lib.mul_Mul_basecase" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.logical_Logical" "pearl_multiprecision_lib.logical_LogicalOld" "pearl_multiprecision_lib.div_Div" "pearl_multiprecision_lib.toom_Toom" "pearl_multiprecision_lib.add_1_Add_1" "pearl_multiprecision_lib.sub_1_Sub_1"
begin
definition redc :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "redc ur u n m \<longleftrightarrow> ur emod m = ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i n * u emod m" for ur u n m
theorem win_size'vc:
  fixes eb :: "32 word"
  fixes o1 :: "bool"
  fixes result :: "32 word"
  assumes fact0: "sint eb = sint (0 :: 32 word) \<longrightarrow> o1 = True"
  assumes fact1: "o1 = True \<longrightarrow> eb = (0 :: 32 word)"
  assumes fact2: "if o1 = True then result = (0 :: 32 word) else if sint eb \<le> (7 :: int) then result = (1 :: 32 word) else if sint eb \<le> (25 :: int) then result = (2 :: 32 word) else if sint eb \<le> (81 :: int) then result = (3 :: 32 word) else if sint eb \<le> (214 :: int) then result = (4 :: 32 word) else if sint eb \<le> (673 :: int) then result = (5 :: 32 word) else if sint eb \<le> (1793 :: int) then result = (6 :: 32 word) else if sint eb \<le> (4609 :: int) then result = (7 :: 32 word) else if sint eb \<le> (11521 :: int) then result = (8 :: 32 word) else if sint eb \<le> (28161 :: int) then result = (9 :: 32 word) else result = (10 :: 32 word)"
  shows "(0 :: int) \<le> sint result"
  and "sint result \<le> (10 :: int)"
  and "(0 :: int) < sint eb \<longrightarrow> (0 :: int) < sint result"
  sorry
end
