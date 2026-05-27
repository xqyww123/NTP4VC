theory A_Strchrnul_A_Strchrnul
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint" "A_Strlen_A_Strlen"
begin
consts l_strchrnul :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> addr"
axiomatization where fix_l_strchrnul:   "if mchar_0 str_0 = c then l_strchrnul mchar_0 str_0 c = str_0 else if mchar_0 str_0 = (0 :: int) then l_strchrnul mchar_0 str_0 c = str_0 else l_strchrnul mchar_0 (shift str_0 (1 :: int)) c = l_strchrnul mchar_0 str_0 c"
  for mchar_0 :: "addr \<Rightarrow> int"
  and str_0 :: "addr"
  and c :: "int"
end
