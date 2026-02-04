theory div_Div
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/lemmas_Lemmas" "../../lib/isabelle/compare_Compare" "../../lib/isabelle/util_Util" "../../lib/isabelle/ptralias_Alias" "../../lib/isabelle/util_UtilOld" "../../lib/isabelle/add_Add" "../../lib/isabelle/add_AddOld" "../../lib/isabelle/sub_SubOld" "../../lib/isabelle/logical_LogicalUtil" "../../lib/isabelle/logical_LogicalOld" "../../lib/isabelle/mul_Mul"
begin
definition reciprocal :: "64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal v d \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv uint d - ((18446744073709551615 :: int) + (1 :: int))" for v d
definition reciprocal_3by2 :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> _"
  where "reciprocal_3by2 v dh dl \<longleftrightarrow> uint v = (((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) * ((18446744073709551615 :: int) + (1 :: int)) - (1 :: int)) ediv (uint dl + ((18446744073709551615 :: int) + (1 :: int)) * uint dh) - ((18446744073709551615 :: int) + (1 :: int))" for v dh dl
definition normalized :: "64 word ptr \<Rightarrow> 32 word \<Rightarrow> _"
  where "normalized x sz \<longleftrightarrow> valid x (sint sz) \<and> ((18446744073709551615 :: int) + (1 :: int)) ediv (2 :: int) \<le> uint (pelts x (offset x + sint sz - (1 :: int)))" for x sz
end
