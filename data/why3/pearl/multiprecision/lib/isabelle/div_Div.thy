theory div_Div
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "types_Config" "types_Types" "types_Int32Eq" "types_UInt64Eq" "lemmas_Lemmas" "compare_Compare" "util_Util" "ptralias_Alias" "util_UtilOld" "add_Add" "add_AddOld" "sub_SubOld" "logical_LogicalUtil" "logical_LogicalOld" "mul_Mul"
begin
definition reciprocal :: "64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal v d \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv uint d - ((18446744073709551615 :: int) + (1 :: int))" for v d
definition reciprocal_3by2 :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal_3by2 v dh dl \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv (uint dl + ((18446744073709551615 :: int) + (1 :: int)) * uint dh) - ((18446744073709551615 :: int) + (1 :: int))" for v dh dl
definition normalized :: "64 word ptr \<Rightarrow> 32 word \<Rightarrow> _"
  where "normalized x sz \<longleftrightarrow> valid x (sint sz) \<and> ((18446744073709551615 :: int) + (1 :: int)) ediv (2 :: int) \<le> uint (pelts x (offset x + sint sz - (1 :: int)))" for x sz
end
