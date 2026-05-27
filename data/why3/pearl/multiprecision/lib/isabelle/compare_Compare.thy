theory compare_Compare
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "types_Config" "types_Types" "types_Int32Eq" "types_UInt64Eq" "lemmas_Lemmas"
begin
definition compare_int :: "int \<Rightarrow> int \<Rightarrow> int"
  where "compare_int x y = (if x < y then -(1 :: int) else if x = y then 0 :: int else (1 :: int))" for x y
end
