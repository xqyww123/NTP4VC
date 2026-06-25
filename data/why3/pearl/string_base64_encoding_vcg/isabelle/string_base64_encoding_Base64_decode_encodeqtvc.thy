theory string_base64_encoding_Base64_decode_encodeqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.string_StringBuffer"
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
definition encoding :: "string \<Rightarrow> string \<Rightarrow> _"
  where "encoding s1 s2 \<longleftrightarrow> int (length s2) = (int (length s1) + calc_pad s1) cdiv (3 :: int) * (4 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s2) cdiv (4 :: int) \<longrightarrow> (case (s2 ! nat ((4 :: int) * i), s2 ! nat ((4 :: int) * i + (1 :: int)), s2 ! nat ((4 :: int) * i + (2 :: int)), s2 ! nat ((4 :: int) * i + (3 :: int))) of (b1, b2, b3, b4) \<Rightarrow> s1 ! nat (i * (3 :: int)) = char_of (b642int b1 * (4 :: int) + b642int b2 cdiv (16 :: int)) \<and> (i * (3 :: int) + (1 :: int) < int (length s1) \<longrightarrow> s1 ! nat (i * (3 :: int) + (1 :: int)) = char_of (b642int b2 cmod (16 :: int) * (16 :: int) + b642int b3 cdiv (4 :: int))) \<and> (i * (3 :: int) + (2 :: int) < int (length s1) \<longrightarrow> s1 ! nat (i * (3 :: int) + (2 :: int)) = char_of (b642int b3 cmod (4 :: int) * (64 :: int) + b642int b4)))) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s2) - get_pad s2 \<longrightarrow> valid_b64_char (s2 ! nat i)) \<and> (get_pad s2 = (1 :: int) \<longrightarrow> b642int (s2 ! nat (int (length s2) - (2 :: int))) cmod (4 :: int) = (0 :: int) \<and> s2 ! nat (int (length s2) - (1 :: int)) = char_of (sint (61 :: 63 word))) \<and> (get_pad s2 = (2 :: int) \<longrightarrow> b642int (s2 ! nat (int (length s2) - (3 :: int))) cmod (16 :: int) = (0 :: int) \<and> s2 ! nat (int (length s2) - (2 :: int)) = s2 ! nat (int (length s2) - (1 :: int)) \<and> s2 ! nat (int (length s2) - (1 :: int)) = char_of (sint (61 :: 63 word))) \<and> calc_pad s1 = get_pad s2" for s1 s2
definition valid_b64 :: "string \<Rightarrow> _"
  where "valid_b64 s \<longleftrightarrow> int (length s) cmod (4 :: int) = (0 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < int (length s) - get_pad s \<longrightarrow> valid_b64_char (s ! nat i)) \<and> (get_pad s = (1 :: int) \<longrightarrow> b642int (s ! nat (int (length s) - (2 :: int))) cmod (4 :: int) = (0 :: int) \<and> s ! nat (int (length s) - (1 :: int)) = char_of (sint (61 :: 63 word))) \<and> (get_pad s = (2 :: int) \<longrightarrow> b642int (s ! nat (int (length s) - (3 :: int))) cmod (16 :: int) = (0 :: int) \<and> s ! nat (int (length s) - (2 :: int)) = char_of (sint (61 :: 63 word)) \<and> s ! nat (int (length s) - (1 :: int)) = char_of (sint (61 :: 63 word)))" for s
theorem decode_encode'vc:
  fixes s :: "string"
  fixes s1 :: "string"
  assumes fact0: "encoding s s1"
  shows "valid_b64 s1"
  sorry
end
