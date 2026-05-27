theory logical_LogicalUtil_lsl_mod_extqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem lsl_mod_ext'vc:
  fixes cnt :: "64 word"
  fixes x :: "64 word"
  assumes fact0: "(0 :: int) \<le> uint cnt"
  assumes fact1: "uint cnt < (64 :: int)"
  shows "(0 :: int) \<le> uint cnt"
  and "uint cnt < (64 :: int)"
  and "\<forall>(r :: 64 word). uint r = uint x * (2 :: int) ^\<^sub>i uint cnt emod ((18446744073709551615 :: int) + (1 :: int)) \<longrightarrow> \<not>(18446744073709551615 :: int) + (1 :: int) = (0 :: int) \<and> uint r = uint x * (2 :: int) ^\<^sub>i uint cnt emod ((18446744073709551615 :: int) + (1 :: int)) \<and> uint r \<le> (18446744073709551615 :: int) + (1 :: int) - (2 :: int) ^\<^sub>i uint cnt"
  sorry
end
