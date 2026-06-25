theory string_hex_encoding_Top_decodeqtvc
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
theorem decode'vc:
  fixes s :: "string"
  fixes o1 :: "63 word"
  assumes fact0: "valid_hex s"
  assumes fact1: "sint o1 = int (length s)"
  assumes fact2: "(0 :: int) \<le> int (length s)"
  shows "\<not>(2 :: int) = (0 :: int)"
  and "int'63_in_bounds (sint o1 cdiv (2 :: int))"
  and "\<forall>(o2 :: 63 word). sint o2 = sint o1 cdiv (2 :: int) \<longrightarrow> (\<forall>(r :: buffer). str r = '''' \<longrightarrow> ((0 :: int) cmod (2 :: int) = (0 :: int) \<and> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> int (length s)) \<and> int (length (str r)) = (0 :: int) cdiv (2 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < (0 :: int) cdiv (2 :: int) \<longrightarrow> str r ! nat j = char_of (xeh (s ! nat ((2 :: int) * j)) * (16 :: int) + xeh (s ! nat ((2 :: int) * j + (1 :: int)))))) \<and> (\<forall>(r1 :: buffer) (i :: 63 word). sint i cmod (2 :: int) = (0 :: int) \<and> ((0 :: int) \<le> sint i \<and> sint i \<le> int (length s)) \<and> int (length (str r1)) = sint i cdiv (2 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint i cdiv (2 :: int) \<longrightarrow> str r1 ! nat j = char_of (xeh (s ! nat ((2 :: int) * j)) * (16 :: int) + xeh (s ! nat ((2 :: int) * j + (1 :: int))))) \<longrightarrow> (\<forall>(o3 :: 63 word). sint o3 = int (length s) \<and> (0 :: int) \<le> int (length s) \<longrightarrow> (if sint i < sint o3 then ((0 :: int) \<le> sint i \<and> sint i < int (length s)) \<and> (let o4 :: char = s ! nat (sint i) in valid_hex_char o4 \<and> (\<forall>(v_i :: 63 word). sint v_i = xeh o4 \<longrightarrow> int'63_in_bounds (sint i + (1 :: int)) \<and> (\<forall>(o5 :: 63 word). sint o5 = sint i + (1 :: int) \<longrightarrow> ((0 :: int) \<le> sint o5 \<and> sint o5 < int (length s)) \<and> (let o6 :: char = s ! nat (sint o5) in valid_hex_char o6 \<and> (\<forall>(v_ii :: 63 word). sint v_ii = xeh o6 \<longrightarrow> int'63_in_bounds (sint v_i * (16 :: int)) \<and> (\<forall>(o7 :: 63 word). sint o7 = sint v_i * (16 :: int) \<longrightarrow> int'63_in_bounds (sint o7 + sint v_ii) \<and> (\<forall>(o8 :: 63 word). sint o8 = sint o7 + sint v_ii \<longrightarrow> ((0 :: int) \<le> sint o8 \<and> sint o8 < (256 :: int)) \<and> (\<forall>(r2 :: buffer). str r2 = str r1 @ [char_of (sint o8)] \<longrightarrow> int'63_in_bounds (sint i + (2 :: int)) \<and> (\<forall>(o9 :: 63 word). sint o9 = sint i + (2 :: int) \<longrightarrow> ((0 :: int) \<le> int (length s) - sint i \<and> int (length s) - sint o9 < int (length s) - sint i) \<and> sint o9 cmod (2 :: int) = (0 :: int) \<and> ((0 :: int) \<le> sint o9 \<and> sint o9 \<le> int (length s)) \<and> int (length (str r2)) = sint o9 cdiv (2 :: int) \<and> (\<forall>(j :: int). (0 :: int) \<le> j \<and> j < sint o9 cdiv (2 :: int) \<longrightarrow> str r2 ! nat j = char_of (xeh (s ! nat ((2 :: int) * j)) * (16 :: int) + xeh (s ! nat ((2 :: int) * j + (1 :: int)))))))))))))) else encoding (str r1) s))))"
  sorry
end
