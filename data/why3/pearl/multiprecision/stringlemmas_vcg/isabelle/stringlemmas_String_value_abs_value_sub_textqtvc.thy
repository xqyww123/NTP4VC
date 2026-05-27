theory stringlemmas_String_value_abs_value_sub_textqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "pearl_multiprecision_lib.stringlemmas_String_lemmas" "pearl_multiprecision_lib.lemmas_Lemmas" "mach.int_Unsigned" "mach.c_C" "mach.c_String" "mach.c_UChar" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.stringlemmas_Conversions"
begin
theorem abs_value_sub_text'vc:
  fixes n :: "int"
  fixes m :: "int"
  assumes fact0: "n < m"
  shows "(0 :: int) \<le> m - n"
  and "m - (1 :: int) - n < m - n"
  sorry
end
