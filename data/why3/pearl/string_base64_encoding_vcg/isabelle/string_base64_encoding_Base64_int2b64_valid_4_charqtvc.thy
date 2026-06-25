theory string_base64_encoding_Base64_int2b64_valid_4_charqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.string_StringBuffer"
begin
definition int2b64 :: "int \<Rightarrow> char"
  where "int2b64 i = (if (0 :: int) \<le> i \<and> i \<le> (25 :: int) then char_of (i + (65 :: int)) else if (26 :: int) \<le> i \<and> i \<le> (51 :: int) then char_of (i - (26 :: int) + (97 :: int)) else if (52 :: int) \<le> i \<and> i \<le> (61 :: int) then char_of (i - (52 :: int) + (48 :: int)) else if i = (62 :: int) then char_of (43 :: int) else if i = (63 :: int) then char_of (47 :: int) else char_of (0 :: int))" for i
definition valid_b64_char :: "char \<Rightarrow> _"
  where "valid_b64_char c \<longleftrightarrow> (65 :: int) \<le> char_code c \<and> char_code c \<le> (90 :: int) \<or> (97 :: int) \<le> char_code c \<and> char_code c \<le> (122 :: int) \<or> (48 :: int) \<le> char_code c \<and> char_code c \<le> (57 :: int) \<or> char_code c = (43 :: int) \<or> char_code c = (47 :: int)" for c
theorem int2b64_valid_4_char'vc:
  fixes i :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < (64 :: int)"
  shows "valid_b64_char (int2b64 i)"
  sorry
end
