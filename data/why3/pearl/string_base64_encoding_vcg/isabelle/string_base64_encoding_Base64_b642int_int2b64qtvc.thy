theory string_base64_encoding_Base64_b642int_int2b64qtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.string_StringBuffer"
begin
definition int2b64 :: "int \<Rightarrow> char"
  where "int2b64 i = (if (0 :: int) \<le> i \<and> i \<le> (25 :: int) then char_of (i + (65 :: int)) else if (26 :: int) \<le> i \<and> i \<le> (51 :: int) then char_of (i - (26 :: int) + (97 :: int)) else if (52 :: int) \<le> i \<and> i \<le> (61 :: int) then char_of (i - (52 :: int) + (48 :: int)) else if i = (62 :: int) then char_of (43 :: int) else if i = (63 :: int) then char_of (47 :: int) else char_of (0 :: int))" for i
definition valid_b64_char :: "char \<Rightarrow> _"
  where "valid_b64_char c \<longleftrightarrow> (65 :: int) \<le> char_code c \<and> char_code c \<le> (90 :: int) \<or> (97 :: int) \<le> char_code c \<and> char_code c \<le> (122 :: int) \<or> (48 :: int) \<le> char_code c \<and> char_code c \<le> (57 :: int) \<or> char_code c = (43 :: int) \<or> char_code c = (47 :: int)" for c
definition b642int :: "char \<Rightarrow> int"
  where "b642int c = (if (65 :: int) \<le> char_code c \<and> char_code c \<le> (90 :: int) then char_code c - (65 :: int) else if (97 :: int) \<le> char_code c \<and> char_code c \<le> (122 :: int) then char_code c - (97 :: int) + (26 :: int) else if (48 :: int) \<le> char_code c \<and> char_code c \<le> (57 :: int) then char_code c - (48 :: int) + (52 :: int) else if char_code c = (43 :: int) then 62 :: int else if char_code c = (47 :: int) then 63 :: int else if c = char_of (sint (61 :: 63 word)) then 0 :: int else (64 :: int))" for c
theorem b642int_int2b64'vc:
  fixes i :: "int"
  assumes fact0: "(0 :: int) \<le> i"
  assumes fact1: "i < (64 :: int)"
  shows "b642int (int2b64 i) = i"
  sorry
end
