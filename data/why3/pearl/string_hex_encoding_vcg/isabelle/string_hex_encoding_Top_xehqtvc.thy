theory string_hex_encoding_Top_xehqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.string_StringBuffer"
begin
definition valid_hex_char :: "char \<Rightarrow> _"
  where "valid_hex_char c \<longleftrightarrow> (48 :: int) \<le> char_code c \<and> char_code c < (58 :: int) \<or> (65 :: int) \<le> char_code c \<and> char_code c < (71 :: int)" for c
definition hex :: "int \<Rightarrow> char"
  where "hex i = (if (0 :: int) \<le> i \<and> i < (10 :: int) then char_of (i + (48 :: int)) else if (10 :: int) \<le> i \<and> i < (16 :: int) then char_of (i + (55 :: int)) else [CHR 0x0] ! (0 :: nat))" for i
definition xeh :: "char \<Rightarrow> int"
  where "xeh c = (if (48 :: int) \<le> char_code c \<and> char_code c < (58 :: int) then char_code c - (48 :: int) else if (65 :: int) \<le> char_code c \<and> char_code c < (71 :: int) then char_code c - (55 :: int) else -(1 :: int))" for c
theorem xeh'vc:
  fixes c :: "char"
  fixes q1' :: "63 word"
  fixes o1 :: "bool"
  assumes fact0: "valid_hex_char c"
  assumes fact1: "sint q1' = char_code c"
  assumes fact2: "if (48 :: int) \<le> sint q1' then o1 = (if sint q1' < (58 :: int) then True else False) else o1 = False"
  shows "if o1 = True then \<forall>(o2 :: 63 word). sint o2 = char_code c \<longrightarrow> int'63_in_bounds (sint o2 - (48 :: int)) else \<forall>(o2 :: 63 word). sint o2 = char_code c \<longrightarrow> int'63_in_bounds (sint o2 - (55 :: int))"
  and "\<forall>(result :: 63 word). (if o1 = True then \<exists>(o2 :: 63 word). sint o2 = char_code c \<and> sint result = sint o2 - (48 :: int) else \<exists>(o2 :: 63 word). sint o2 = char_code c \<and> sint result = sint o2 - (55 :: int)) \<longrightarrow> sint result = xeh c"
  sorry
end
