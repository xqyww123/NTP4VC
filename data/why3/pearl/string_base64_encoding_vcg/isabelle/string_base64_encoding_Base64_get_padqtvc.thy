theory string_base64_encoding_Base64_get_padqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.string_StringBuffer"
begin
definition int2b64 :: "int \<Rightarrow> char"
  where "int2b64 i = (if (0 :: int) \<le> i \<and> i \<le> (25 :: int) then char_of (i + (65 :: int)) else if (26 :: int) \<le> i \<and> i \<le> (51 :: int) then char_of (i - (26 :: int) + (97 :: int)) else if (52 :: int) \<le> i \<and> i \<le> (61 :: int) then char_of (i - (52 :: int) + (48 :: int)) else if i = (62 :: int) then char_of (43 :: int) else if i = (63 :: int) then char_of (47 :: int) else char_of (0 :: int))" for i
definition valid_b64_char :: "char \<Rightarrow> _"
  where "valid_b64_char c \<longleftrightarrow> (65 :: int) \<le> char_code c \<and> char_code c \<le> (90 :: int) \<or> (97 :: int) \<le> char_code c \<and> char_code c \<le> (122 :: int) \<or> (48 :: int) \<le> char_code c \<and> char_code c \<le> (57 :: int) \<or> char_code c = (43 :: int) \<or> char_code c = (47 :: int)" for c
definition b642int :: "char \<Rightarrow> int"
  where "b642int c = (if (65 :: int) \<le> char_code c \<and> char_code c \<le> (90 :: int) then char_code c - (65 :: int) else if (97 :: int) \<le> char_code c \<and> char_code c \<le> (122 :: int) then char_code c - (97 :: int) + (26 :: int) else if (48 :: int) \<le> char_code c \<and> char_code c \<le> (57 :: int) then char_code c - (48 :: int) + (52 :: int) else if char_code c = (43 :: int) then 62 :: int else if char_code c = (47 :: int) then 63 :: int else if c = char_of (sint (61 :: 63 word)) then 0 :: int else (64 :: int))" for c
definition get_pad :: "string \<Rightarrow> int"
  where "get_pad s = (if (1 :: int) \<le> int (length s) \<and> s ! nat (int (length s) - (1 :: int)) = char_of (sint (61 :: 63 word)) then if (2 :: int) \<le> int (length s) \<and> s ! nat (int (length s) - (2 :: int)) = char_of (sint (61 :: 63 word)) then 2 :: int else (1 :: int) else (0 :: int))" for s
theorem get_pad'vc:
  fixes o1 :: "63 word"
  fixes s :: "string"
  assumes fact0: "sint o1 = int (length s)"
  assumes fact1: "(0 :: int) \<le> int (length s)"
  shows "if (1 :: int) \<le> sint o1 then \<forall>(o2 :: 63 word). sint o2 = int (length s) \<and> (0 :: int) \<le> int (length s) \<longrightarrow> int'63_in_bounds (sint o2 - (1 :: int)) \<and> (\<forall>(o3 :: 63 word). sint o3 = sint o2 - (1 :: int) \<longrightarrow> ((0 :: int) \<le> sint o3 \<and> sint o3 < int (length s)) \<and> (if s ! nat (sint o3) = char_of (sint (61 :: 63 word)) then \<forall>(o4 :: 63 word). sint o4 = int (length s) \<and> (0 :: int) \<le> int (length s) \<longrightarrow> (if (2 :: int) \<le> sint o4 then \<forall>(o5 :: 63 word). sint o5 = int (length s) \<and> (0 :: int) \<le> int (length s) \<longrightarrow> int'63_in_bounds (sint o5 - (2 :: int)) \<and> (\<forall>(o6 :: 63 word). sint o6 = sint o5 - (2 :: int) \<longrightarrow> ((0 :: int) \<le> sint o6 \<and> sint o6 < int (length s)) \<and> (\<forall>(result :: 63 word). (if s ! nat (sint o6) = char_of (sint (61 :: 63 word)) then result = (2 :: 63 word) else result = (1 :: 63 word)) \<longrightarrow> sint result = get_pad s)) else sint (1 :: 63 word) = get_pad s) else (0 :: int) = get_pad s)) else (0 :: int) = get_pad s"
  sorry
end
