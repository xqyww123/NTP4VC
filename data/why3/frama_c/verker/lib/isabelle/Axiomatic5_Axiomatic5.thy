theory Axiomatic5_Axiomatic5
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound"
begin
definition p_kstrtobool_fmt_false :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_kstrtobool_fmt_false mchar_0 s \<longleftrightarrow> (let x :: int = mchar_0 (shift s (0 :: int)); x_1 :: int = mchar_0 (shift s (1 :: int)) in x = (48 :: int) \<or> x = (78 :: int) \<or> x = (110 :: int) \<or> (x = (79 :: int) \<or> x = (111 :: int)) \<and> (x_1 = (70 :: int) \<or> x_1 = (102 :: int)))" for mchar_0 s
definition p_kstrtobool_fmt_true :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_kstrtobool_fmt_true mchar_0 s \<longleftrightarrow> (let x :: int = mchar_0 (shift s (0 :: int)); x_1 :: int = mchar_0 (shift s (1 :: int)) in x = (49 :: int) \<or> x = (89 :: int) \<or> x = (121 :: int) \<or> (x = (79 :: int) \<or> x = (111 :: int)) \<and> (x_1 = (78 :: int) \<or> x_1 = (110 :: int)))" for mchar_0 s
definition p_kstrtobool_fmt :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> _"
  where "p_kstrtobool_fmt mchar_0 s \<longleftrightarrow> p_kstrtobool_fmt_false mchar_0 s \<or> p_kstrtobool_fmt_true mchar_0 s" for mchar_0 s
end
