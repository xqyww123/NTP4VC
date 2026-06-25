theory string_hex_encoding_Top_decode_uniqueqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.string_StringBuffer"
begin
definition valid_hex_char :: "char \<Rightarrow> _"
  where "valid_hex_char c \<longleftrightarrow> (48 :: int) \<le> char_code c \<and> char_code c < (58 :: int) \<or> (65 :: int) \<le> char_code c \<and> char_code c < (71 :: int)" for c
definition hex :: "int \<Rightarrow> char"
  where "hex i = (if (0 :: int) \<le> i \<and> i < (10 :: int) then char_of (i + (48 :: int)) else if (10 :: int) \<le> i \<and> i < (16 :: int) then char_of (i + (55 :: int)) else [CHR 0x0] ! (0 :: nat))" for i
definition xeh :: "char \<Rightarrow> int"
  where "xeh c = (if (48 :: int) \<le> char_code c \<and> char_code c < (58 :: int) then char_code c - (48 :: int) else if (65 :: int) \<le> char_code c \<and> char_code c < (71 :: int) then char_code c - (55 :: int) else -(1 :: int))" for c
definition valid_hex :: "string \<Rightarrow> _"
  where "valid_hex s \<longleftrightarrow> int (length s) cmod (2 :: int) = (0 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) \<longrightarrow> valid_hex_char (s ! nat i))" for s
definition encoding :: "string \<Rightarrow> string \<Rightarrow> _"
  where "encoding s1 s2 \<longleftrightarrow> int (length s2) = (2 :: int) * int (length s1) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s1) \<longrightarrow> s1 ! nat i = char_of (xeh (s2 ! nat ((2 :: int) * i)) * (16 :: int) + xeh (s2 ! nat ((2 :: int) * i + (1 :: int))))) \<and> valid_hex s2" for s1 s2
theorem decode_unique'vc:
  fixes s1 :: "string"
  fixes s2 :: "string"
  fixes s3 :: "string"
  assumes fact0: "encoding s1 s2"
  assumes fact1: "encoding s3 s2"
  shows "s1 = s3"
  sorry
end
