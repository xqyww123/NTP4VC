theory valuation_Valuation_power_ge_1qtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts valuation :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where valuation_def:   "if n cmod p = (0 :: int) then valuation n p = valuation (n cdiv p) p + (1 :: int) else valuation n p = (0 :: int)"
 if "(1 :: int) < p"
 and "(1 :: int) \<le> n"
  for p :: "int"
  and n :: "int"
axiomatization where valuation'spec'0:   "(0 :: int) \<le> valuation n p"
 if "(1 :: int) < p"
 and "(1 :: int) \<le> n"
  for p :: "int"
  and n :: "int"
axiomatization where valuation'spec:   "p ^\<^sub>i valuation n p dvd n"
 if "(1 :: int) < p"
 and "(1 :: int) \<le> n"
  for p :: "int"
  and n :: "int"
theorem power_ge_1'vc:
  fixes b :: "int"
  fixes e :: "int"
  assumes fact0: "(1 :: int) \<le> b"
  assumes fact1: "(0 :: int) \<le> e"
  shows "(1 :: int) \<le> b ^\<^sub>i e"
  sorry
end
