theory string_hex_encoding_Top_hexqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.string_StringBuffer"
begin
definition valid_hex_char :: "char \<Rightarrow> _"
  where "valid_hex_char c \<longleftrightarrow> (48 :: int) \<le> char_code c \<and> char_code c < (58 :: int) \<or> (65 :: int) \<le> char_code c \<and> char_code c < (71 :: int)" for c
definition hex :: "int \<Rightarrow> char"
  where "hex i = (if (0 :: int) \<le> i \<and> i < (10 :: int) then char_of (i + (48 :: int)) else if (10 :: int) \<le> i \<and> i < (16 :: int) then char_of (i + (55 :: int)) else [CHR 0x0] ! (0 :: nat))" for i
theorem hex'vc:
  fixes i :: "63 word"
  assumes fact0: "(0 :: int) \<le> sint i"
  assumes fact1: "sint i < (16 :: int)"
  shows "if sint i < (10 :: int) then int'63_in_bounds (sint i + (48 :: int)) \<and> (\<forall>(o1 :: 63 word). sint o1 = sint i + (48 :: int) \<longrightarrow> (0 :: int) \<le> sint o1 \<and> sint o1 < (256 :: int)) else int'63_in_bounds (sint i + (55 :: int)) \<and> (\<forall>(o1 :: 63 word). sint o1 = sint i + (55 :: int) \<longrightarrow> (0 :: int) \<le> sint o1 \<and> sint o1 < (256 :: int))"
  and "\<forall>(result :: char). (if sint i < (10 :: int) then \<exists>(o1 :: 63 word). sint o1 = sint i + (48 :: int) \<and> result = char_of (sint o1) else \<exists>(o1 :: 63 word). sint o1 = sint i + (55 :: int) \<and> result = char_of (sint o1)) \<longrightarrow> result = hex (sint i)"
  sorry
end
