theory A_Strnlen_A_Strnlen
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint" "A_Strlen_A_Strlen"
begin
definition p_valid_strn :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> _"
  where "p_valid_strn malloc_0 mchar_0 s cnt_0 \<longleftrightarrow> (let a :: addr = shift s (0 :: int) in valid_rw malloc_0 a ((1 :: int) + cnt_0) \<or> (\<exists>(i :: int). mchar_0 (shift s i) = (0 :: int) \<and> i < cnt_0 \<and> is_uint64 i \<and> valid_rw malloc_0 a ((1 :: int) + i)) \<and> (\<forall>(j :: int). j \<le> cnt_0 \<longrightarrow> is_sint8 (mchar_0 (shift s j))))" for malloc_0 mchar_0 s cnt_0
consts l_strnlen :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int"
axiomatization where fix_l_strnlen:   "if cnt_0 = (0 :: int) \<or> mchar_0 (shift s (0 :: int)) = (0 :: int) then l_strnlen mchar_0 s cnt_0 = (0 :: int) else to_uint64 ((1 :: int) + l_strnlen mchar_0 (shift s (1 :: int)) (to_uint64 (cnt_0 - (1 :: int)))) = l_strnlen mchar_0 s cnt_0"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and cnt_0 :: "int"
axiomatization where Q_TL_strnlen:   "is_uint64 (l_strnlen mchar_0 s cnt_0)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
  and cnt_0 :: "int"
end
