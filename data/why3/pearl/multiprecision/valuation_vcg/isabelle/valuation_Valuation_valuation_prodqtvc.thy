theory valuation_Valuation_valuation_prodqtvc
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
theorem valuation_prod'vc:
  fixes n1 :: "int"
  fixes n2 :: "int"
  fixes p :: "int"
  assumes fact0: "(1 :: int) \<le> n1"
  assumes fact1: "(1 :: int) \<le> n2"
  assumes fact2: "prime p"
  shows "valuation (n1 * n2) p = valuation n1 p + valuation n2 p"
  sorry
end
