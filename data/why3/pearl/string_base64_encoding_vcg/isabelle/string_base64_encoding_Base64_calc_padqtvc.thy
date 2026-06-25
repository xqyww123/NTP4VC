theory string_base64_encoding_Base64_calc_padqtvc
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
definition calc_pad :: "string \<Rightarrow> int"
  where "calc_pad s = (if int (length s) cmod (3 :: int) = (1 :: int) then 2 :: int else if int (length s) cmod (3 :: int) = (2 :: int) then 1 :: int else (0 :: int))" for s
theorem calc_pad'vc:
  fixes o1 :: "63 word"
  fixes s :: "string"
  assumes fact0: "sint o1 = int (length s)"
  assumes fact1: "(0 :: int) \<le> int (length s)"
  shows "\<not>(3 :: int) = (0 :: int)"
  and "int'63_in_bounds (sint o1 cmod (3 :: int))"
  and "\<forall>(o2 :: 63 word). sint o2 = sint o1 cmod (3 :: int) \<longrightarrow> (sint o2 = (1 :: int) \<longrightarrow> o2 = (1 :: 63 word)) \<longrightarrow> (if o2 = (1 :: 63 word) then (2 :: int) = calc_pad s else \<forall>(o3 :: 63 word). sint o3 = int (length s) \<and> (0 :: int) \<le> int (length s) \<longrightarrow> (\<not>(3 :: int) = (0 :: int) \<and> int'63_in_bounds (sint o3 cmod (3 :: int))) \<and> (\<forall>(o4 :: 63 word). sint o4 = sint o3 cmod (3 :: int) \<longrightarrow> (sint o4 = (2 :: int) \<longrightarrow> o4 = (2 :: 63 word)) \<longrightarrow> (\<forall>(result :: 63 word). (if o4 = (2 :: 63 word) then result = (1 :: 63 word) else result = (0 :: 63 word)) \<longrightarrow> sint result = calc_pad s)))"
  sorry
end
