theory stringlemmas_Conversions_digitsubupqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "pearl_multiprecision_lib.lemmas_Lemmas" "mach.int_Unsigned" "mach.c_C" "mach.c_String" "mach.c_UChar" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq"
begin
definition num_to_lowercase_text :: "8 word \<Rightarrow> char"
  where "num_to_lowercase_text d = (if (0 :: int) \<le> uint d \<and> uint d < (36 :: int) then ''0123456789abcdefghijklmnopqrstuvwxyz'' ! nat (uint d) else char_of (-(1 :: int)))" for d
definition to_lowercase_text :: "(int \<Rightarrow> 8 word) \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "to_lowercase_text d t m n \<longleftrightarrow> (\<forall>(i :: int). n \<le> i \<and> i < m \<longrightarrow> t i = num_to_lowercase_text (d i))" for d t m n
definition num_to_uppercase_text :: "8 word \<Rightarrow> char"
  where "num_to_uppercase_text d = (if (0 :: int) \<le> uint d \<and> uint d < (36 :: int) then ''0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'' ! nat (uint d) else char_of (-(1 :: int)))" for d
definition to_uppercase_text :: "(int \<Rightarrow> 8 word) \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "to_uppercase_text d t m n \<longleftrightarrow> (\<forall>(i :: int). n \<le> i \<and> i < m \<longrightarrow> t i = num_to_uppercase_text (d i))" for d t m n
definition num_to_bothcase_text :: "8 word \<Rightarrow> char"
  where "num_to_bothcase_text d = (if (0 :: int) \<le> uint d \<and> uint d < (62 :: int) then ''0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'' ! nat (uint d) else char_of (-(1 :: int)))" for d
definition to_bothcase_text :: "(int \<Rightarrow> 8 word) \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "to_bothcase_text d t m n \<longleftrightarrow> (\<forall>(i :: int). n \<le> i \<and> i < m \<longrightarrow> t i = num_to_bothcase_text (d i))" for d t m n
theorem digitsubup'vc:
  shows "''0123456789'' = drop (0 :: nat) (take ((10 :: nat) - (0 :: nat)) ''0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'')"
  sorry
end
