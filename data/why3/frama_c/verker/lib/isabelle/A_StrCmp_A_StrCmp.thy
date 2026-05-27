theory A_StrCmp_A_StrCmp
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint" "A_Strlen_A_Strlen"
begin
definition l_cmp :: "int \<Rightarrow> int \<Rightarrow> int"
  where "l_cmp a b = (if b = a then 0 :: int else if a < b then -(1 :: int) else (1 :: int))" for a b
consts l_strncmp_1' :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int"
axiomatization where fix_l_strncmp_1':   "if n = -(1 :: int) then l_strncmp_1' mchar_0 cs_0 ct_0 n = (0 :: int) else if mchar_0 (shift ct_0 (0 :: int)) = mchar_0 (shift cs_0 (0 :: int)) then l_strncmp_1' mchar_0 (shift cs_0 (1 :: int)) (shift ct_0 (1 :: int)) (n - (1 :: int)) = l_strncmp_1' mchar_0 cs_0 ct_0 n else l_cmp (to_uint8 (mchar_0 (shift cs_0 (0 :: int)))) (to_uint8 (mchar_0 (shift ct_0 (0 :: int)))) = l_strncmp_1' mchar_0 cs_0 ct_0 n"
  for mchar_0 :: "addr \<Rightarrow> int"
  and cs_0 :: "addr"
  and ct_0 :: "addr"
  and n :: "int"
definition l_strcmp :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int"
  where "l_strcmp mchar_0 cs_0 ct_0 = l_strncmp_1' mchar_0 cs_0 ct_0 (l_strlen mchar_0 cs_0)" for mchar_0 cs_0 ct_0
definition p_equaln :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_equaln mchar_0 cs_0 ct_0 n \<longleftrightarrow> l_strncmp_1' mchar_0 cs_0 ct_0 n = (0 :: int)" for mchar_0 cs_0 ct_0 n
definition p_equal :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> _"
  where "p_equal mchar_0 cs_0 ct_0 \<longleftrightarrow> l_strcmp mchar_0 cs_0 ct_0 = (0 :: int)" for mchar_0 cs_0 ct_0
end
