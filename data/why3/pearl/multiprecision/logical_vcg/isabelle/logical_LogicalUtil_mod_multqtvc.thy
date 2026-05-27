theory logical_LogicalUtil_mod_multqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem mod_mult'vc:
  fixes x :: "int"
  fixes y :: "int"
  fixes z :: "int"
  assumes fact0: "(0 :: int) < x"
  shows "(x * y + z) emod x = z emod x"
  sorry
end
