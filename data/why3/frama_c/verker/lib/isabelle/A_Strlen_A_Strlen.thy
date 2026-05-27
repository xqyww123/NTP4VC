theory A_Strlen_A_Strlen
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint"
begin
definition p_valid_str :: "(int \<Rightarrow> int) \<Rightarrow> (addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_valid_str malloc_0 mchar_0 s \<longleftrightarrow> (\<exists>(i :: int). mchar_0 (shift s i) = (0 :: int) \<and> is_uint64 i \<and> valid_rw malloc_0 (shift s (0 :: int)) ((1 :: int) + i) \<and> (\<forall>(j :: int). j \<le> i \<longrightarrow> is_sint8 (mchar_0 (shift s j))))" for malloc_0 mchar_0 s
consts l_strlen :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int"
axiomatization where fix_l_strlen:   "if mchar_0 (shift s (0 :: int)) = (0 :: int) then l_strlen mchar_0 s = (0 :: int) else to_uint64 ((1 :: int) + l_strlen mchar_0 (shift s (1 :: int))) = l_strlen mchar_0 s"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
axiomatization where Q_TL_strlen:   "is_uint64 (l_strlen mchar_0 s)"
  for mchar_0 :: "addr \<Rightarrow> int"
  and s :: "addr"
end
