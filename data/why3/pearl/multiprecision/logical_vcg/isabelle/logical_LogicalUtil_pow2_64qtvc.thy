theory logical_LogicalUtil_pow2_64qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem pow2_64'vc:
  shows "(2 :: int) ^\<^sub>i (64 :: int) = (18446744073709551615 :: int) + (1 :: int)"
  sorry
end
