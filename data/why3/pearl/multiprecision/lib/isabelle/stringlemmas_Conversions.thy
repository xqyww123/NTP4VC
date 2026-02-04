theory stringlemmas_Conversions
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "../../lib/isabelle/lemmas_Lemmas" "mach.int_Unsigned" "mach.c_C" "mach.c_String" "mach.c_UChar" "../../lib/isabelle/types_Config" "../../lib/isabelle/types_Types" "../../lib/isabelle/types_Int32Eq" "../../lib/isabelle/types_UInt64Eq"
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
definition text_to_num_onecase :: "char \<Rightarrow> int"
  where "text_to_num_onecase c = (if of_char (''0'' ! (0 :: nat)) \<le> of_char c \<and> of_char c \<le> of_char (''9'' ! (0 :: nat)) then of_char c - of_char (''0'' ! (0 :: nat)) else if of_char (''a'' ! (0 :: nat)) \<le> of_char c \<and> of_char c \<le> of_char (''z'' ! (0 :: nat)) then of_char c - of_char (''a'' ! (0 :: nat)) + (10 :: int) else if of_char (''A'' ! (0 :: nat)) \<le> of_char c \<and> of_char c \<le> of_char (''Z'' ! (0 :: nat)) then of_char c - of_char (''A'' ! (0 :: nat)) + (10 :: int) else -(1 :: int))" for c
definition text_to_num_bothcase :: "char \<Rightarrow> int"
  where "text_to_num_bothcase c = (if of_char (''0'' ! (0 :: nat)) \<le> of_char c \<and> of_char c \<le> of_char (''9'' ! (0 :: nat)) then of_char c - of_char (''0'' ! (0 :: nat)) else if of_char (''a'' ! (0 :: nat)) \<le> of_char c \<and> of_char c \<le> of_char (''z'' ! (0 :: nat)) then of_char c - of_char (''a'' ! (0 :: nat)) + (36 :: int) else if of_char (''A'' ! (0 :: nat)) \<le> of_char c \<and> of_char c \<le> of_char (''Z'' ! (0 :: nat)) then of_char c - of_char (''A'' ! (0 :: nat)) + (10 :: int) else -(1 :: int))" for c
definition text_to_num :: "int \<Rightarrow> char \<Rightarrow> int"
  where "text_to_num base c = (if -(36 :: int) \<le> base \<and> base \<le> (36 :: int) then text_to_num_onecase c else text_to_num_bothcase c)" for base c
definition num_to_text :: "int \<Rightarrow> 8 word \<Rightarrow> char"
  where "num_to_text base d = (if (0 :: int) \<le> base \<and> base \<le> (36 :: int) then num_to_lowercase_text d else if (36 :: int) < base \<and> base \<le> (62 :: int) then num_to_bothcase_text d else if -(36 :: int) \<le> base then num_to_uppercase_text d else char_of (-(1 :: int)))" for base d
definition to_num :: "int \<Rightarrow> (int \<Rightarrow> char) \<Rightarrow> (int \<Rightarrow> 8 word) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "to_num base t d n m \<longleftrightarrow> (\<forall>(i :: int). n \<le> i \<and> i < m \<longrightarrow> uint (d i) = text_to_num base (t i))" for base t d n m
end
