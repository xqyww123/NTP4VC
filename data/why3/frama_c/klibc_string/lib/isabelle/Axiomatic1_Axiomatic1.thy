theory Axiomatic1_Axiomatic1
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint" "A_Length_A_Length" "Axiomatic_Axiomatic"
begin
definition p_exists_first_occurence_of_char :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "p_exists_first_occurence_of_char malloc_0 mchar_0 s c pos_0 \<longleftrightarrow> (let x :: int = to_sint8 c; x_1 :: int = l_length mchar_0 s in mchar_0 (shift s pos_0) = x \<and> (0 :: int) \<le> pos_0 \<and> pos_0 \<le> x_1 \<and> -(128 :: int) \<le> c \<and> c \<le> (127 :: int) \<and> valid_rw malloc_0 (shift s (0 :: int)) ((1 :: int) + x_1) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<longrightarrow> i < pos_0 \<longrightarrow> \<not>mchar_0 (shift s i) = x))" for malloc_0 mchar_0 s c pos_0
definition p_char_in_str :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_char_in_str mchar_0 s c \<longleftrightarrow> (\<exists>(i :: int). mchar_0 (shift s i) = c \<and> (0 :: int) \<le> i \<and> i < l_length mchar_0 s)" for mchar_0 s c
end
