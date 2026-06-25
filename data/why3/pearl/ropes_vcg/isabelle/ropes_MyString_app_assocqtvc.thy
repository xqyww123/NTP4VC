theory ropes_MyString_app_assocqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  char
consts dummy_char :: "char"
typedecl  char_string
consts length :: "char_string \<Rightarrow> int"
axiomatization where length'spec:   "(0 :: int) \<le> length x"
  for x :: "char_string"
consts mixfix_lbrb :: "char_string \<Rightarrow> int \<Rightarrow> char"
consts empty :: "char_string"
axiomatization where length_def:   "length empty = (0 :: int)"
definition infix_eqeq :: "char_string \<Rightarrow> char_string \<Rightarrow> _"
  where "infix_eqeq s1 s2 \<longleftrightarrow> length s1 = length s2 \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < length s1 \<longrightarrow> mixfix_lbrb s1 i = mixfix_lbrb s2 i)" for s1 s2
axiomatization where extensionality:   "s1 = s2"
 if "infix_eqeq s1 s2"
  for s1 :: "char_string"
  and s2 :: "char_string"
consts app :: "char_string \<Rightarrow> char_string \<Rightarrow> char_string"
axiomatization where app_def1:   "length (app s1 s2) = length s1 + length s2"
  for s1 :: "char_string"
  and s2 :: "char_string"
axiomatization where app_def2:   "mixfix_lbrb (app s1 s2) i = mixfix_lbrb s1 i"
 if "(0 :: int) \<le> i"
 and "i < length s1"
  for i :: "int"
  and s1 :: "char_string"
  and s2 :: "char_string"
axiomatization where app_def3:   "mixfix_lbrb (app s1 s2) i = mixfix_lbrb s2 (i - length s1)"
 if "length s1 \<le> i"
 and "i < length s1 + length s2"
  for s1 :: "char_string"
  and i :: "int"
  and s2 :: "char_string"
theorem app_assoc'vc:
  fixes s1 :: "char_string"
  fixes s2 :: "char_string"
  fixes s3 :: "char_string"
  shows "infix_eqeq (app s1 (app s2 s3)) (app (app s1 s2) s3)"
  sorry
end
