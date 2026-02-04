theory stringlemmas_String_value
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "../../lib/isabelle/stringlemmas_String_lemmas" "../../lib/isabelle/lemmas_Lemmas" "mach.int_Unsigned" "mach.c_C" "mach.c_String" "mach.c_UChar" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq" "../../lib/isabelle/stringlemmas_Conversions"
begin
consts abs_value_sub_text :: "int \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where abs_value_sub_text'def:   "if n < m then abs_value_sub_text b s n m = text_to_num b (s (m - (1 :: int))) + b * abs_value_sub_text b s n (m - (1 :: int)) else abs_value_sub_text b s n m = (0 :: int)"
  for n :: "int"
  and m :: "int"
  and b :: "int"
  and s :: "int \<Rightarrow> char"
definition abs_value_text :: "int \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int"
  where "abs_value_text b s ofs = abs_value_sub_text b s ofs (ofs + strlen s ofs)" for b s ofs
definition value_text :: "int \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int"
  where "value_text b s ofs = (if s ofs = ''-'' ! (0 :: nat) then -abs_value_text b s (ofs + (1 :: int)) else abs_value_text b s ofs)" for b s ofs
definition text_in_base :: "int \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "text_in_base b t n m \<longleftrightarrow> (\<forall>(i :: int). n \<le> i \<and> i < m \<longrightarrow> (0 :: int) \<le> text_to_num b (t i) \<and> text_to_num b (t i) < b)" for b t n m
definition string_in_base :: "int \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> _"
  where "string_in_base b s ofs \<longleftrightarrow> text_in_base b s ofs (ofs + strlen s ofs) \<and> (0 :: int) < strlen s ofs \<or> s ofs = ''-'' ! (0 :: nat) \<and> text_in_base b s (ofs + (1 :: int)) (ofs + strlen s ofs) \<and> (1 :: int) < strlen s ofs" for b s ofs
end
