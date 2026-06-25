theory string_hex_encoding_Top_encodeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.string_StringBuffer"
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
theorem encode'vc:
  fixes o1 :: "63 word"
  fixes s :: "string"
  fixes r :: "buffer"
  assumes fact0: "sint o1 = int (length s)"
  assumes fact1: "(0 :: int) \<le> int (length s)"
  assumes fact2: "str r = ''''"
  shows "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> int (length s)"
  and "int (length (str r)) = (2 :: int) * (0 :: int)"
  and "\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (0 :: int) \<longrightarrow> str r ! nat ((2 :: int) * j) = hex (char_code (s ! nat j) cdiv (16 :: int)) \<and> str r ! nat ((2 :: int) * j + (1 :: int)) = hex (char_code (s ! nat j) cmod (16 :: int))"
  and "\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (2 :: int) * (0 :: int) \<longrightarrow> valid_hex_char (str r ! nat j)"
  and "\<forall>(r1 :: buffer) (i :: 63 word). ((0 :: int) \<le> sint i \<and> sint i \<le> int (length s)) \<and> int (length (str r1)) = (2 :: int) * sint i \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint i \<longrightarrow> str r1 ! nat ((2 :: int) * j) = hex (char_code (s ! nat j) cdiv (16 :: int)) \<and> str r1 ! nat ((2 :: int) * j + (1 :: int)) = hex (char_code (s ! nat j) cmod (16 :: int))) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (2 :: int) * sint i \<longrightarrow> valid_hex_char (str r1 ! nat j)) \<longrightarrow> (\<forall>(o2 :: 63 word). sint o2 = int (length s) \<and> (0 :: int) \<le> int (length s) \<longrightarrow> (if sint i < sint o2 then ((0 :: int) \<le> sint i \<and> sint i < int (length s)) \<and> (\<forall>(v :: 63 word). sint v = char_code (s ! nat (sint i)) \<longrightarrow> (\<not>(16 :: int) = (0 :: int) \<and> int'63_in_bounds (sint v cdiv (16 :: int))) \<and> (\<forall>(o3 :: 63 word). sint o3 = sint v cdiv (16 :: int) \<longrightarrow> ((0 :: int) \<le> sint o3 \<and> sint o3 < (16 :: int)) \<and> (\<forall>(r2 :: buffer). str r2 = str r1 @ [hex (sint o3)] \<longrightarrow> (\<not>(16 :: int) = (0 :: int) \<and> int'63_in_bounds (sint v cmod (16 :: int))) \<and> (\<forall>(o4 :: 63 word). sint o4 = sint v cmod (16 :: int) \<longrightarrow> ((0 :: int) \<le> sint o4 \<and> sint o4 < (16 :: int)) \<and> (\<forall>(r3 :: buffer). str r3 = str r2 @ [hex (sint o4)] \<longrightarrow> int'63_in_bounds (sint i + (1 :: int)) \<and> (\<forall>(o5 :: 63 word). sint o5 = sint i + (1 :: int) \<longrightarrow> ((0 :: int) \<le> int (length s) - sint i \<and> int (length s) - sint o5 < int (length s) - sint i) \<and> ((0 :: int) \<le> sint o5 \<and> sint o5 \<le> int (length s)) \<and> int (length (str r3)) = (2 :: int) * sint o5 \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint o5 \<longrightarrow> str r3 ! nat ((2 :: int) * j) = hex (char_code (s ! nat j) cdiv (16 :: int)) \<and> str r3 ! nat ((2 :: int) * j + (1 :: int)) = hex (char_code (s ! nat j) cmod (16 :: int))) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (2 :: int) * sint o5 \<longrightarrow> valid_hex_char (str r3 ! nat j)))))))) else encoding s (str r1)))"
  sorry
end
