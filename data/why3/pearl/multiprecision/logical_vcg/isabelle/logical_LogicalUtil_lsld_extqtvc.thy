theory logical_LogicalUtil_lsld_extqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.lemmas_Lemmas"
begin
theorem lsld_ext'vc:
  fixes cnt :: "64 word"
  fixes x :: "64 word"
  assumes fact0: "(0 :: int) < uint cnt"
  assumes fact1: "uint cnt < (64 :: int)"
  shows "(0 :: int) < uint cnt"
  and "uint cnt < (64 :: int)"
  and "\<forall>(r :: 64 word) (d :: 64 word). uint r + ((18446744073709551615 :: int) + (1 :: int)) * uint d = (2 :: int) ^\<^sub>i uint cnt * uint x \<longrightarrow> uint r + ((18446744073709551615 :: int) + (1 :: int)) * uint d = (2 :: int) ^\<^sub>i uint cnt * uint x \<and> uint r emod (2 :: int) ^\<^sub>i uint cnt = (0 :: int) \<and> uint r \<le> (18446744073709551615 :: int) + (1 :: int) - (2 :: int) ^\<^sub>i uint cnt \<and> uint d < (2 :: int) ^\<^sub>i uint cnt"
  sorry
end
