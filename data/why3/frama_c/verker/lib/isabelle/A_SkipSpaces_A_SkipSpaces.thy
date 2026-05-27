theory A_SkipSpaces_A_SkipSpaces
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "A_Strlen_A_Strlen" "Why3STD.Cint_Cint" "A_Ctype_A_Ctype"
begin
consts l_skip_spaces :: "addr \<Rightarrow> addr"
axiomatization where Q_skip_spaces_def:   "if mchar_0 str_0 = (32 :: int) \<or> mchar_0 str_0 = (23654 :: int) \<or> mchar_0 str_0 = (23662 :: int) \<or> mchar_0 str_0 = (23666 :: int) \<or> mchar_0 str_0 = (23668 :: int) then l_skip_spaces (shift str_0 (1 :: int)) = l_skip_spaces str_0 else l_skip_spaces str_0 = str_0"
  for mchar_0 :: "addr \<Rightarrow> int"
  and str_0 :: "addr"
end
