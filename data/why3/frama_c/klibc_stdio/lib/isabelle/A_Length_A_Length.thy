theory A_Length_A_Length
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Axiomatic_Axiomatic" "Compound_Compound"
begin
consts l_length :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int"
axiomatization where Q_string_length:   "l_length mchar_0 s = n"
 if "p_length_of_str_is malloc_0 mchar_0 s n"
  for malloc_0 :: "int \<Rightarrow> int"
  and mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and n :: "int"
end
