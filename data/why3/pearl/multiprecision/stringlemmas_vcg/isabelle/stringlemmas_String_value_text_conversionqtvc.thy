theory stringlemmas_String_value_text_conversionqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "pearl_multiprecision_lib.stringlemmas_String_lemmas" "pearl_multiprecision_lib.lemmas_Lemmas" "mach.int_Unsigned" "mach.c_C" "mach.c_String" "mach.c_UChar" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.stringlemmas_Conversions"
begin
consts abs_value_sub_text :: "int \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where abs_value_sub_text_def:   "if n < m then abs_value_sub_text b s n m = text_to_num b (s (m - (1 :: int))) + b * abs_value_sub_text b s n (m - (1 :: int)) else abs_value_sub_text b s n m = (0 :: int)"
  for n :: "int"
  and m :: "int"
  and b :: "int"
  and s :: "int \<Rightarrow> char"
theorem text_conversion'vc:
  fixes b :: "int"
  fixes t :: "int \<Rightarrow> char"
  fixes d :: "int \<Rightarrow> 8 word"
  fixes n :: "int"
  fixes m :: "int"
  assumes fact0: "to_num b t d n m"
  shows "abs_value_sub_text b t n m = svalue_sub b d n m"
  sorry
end
