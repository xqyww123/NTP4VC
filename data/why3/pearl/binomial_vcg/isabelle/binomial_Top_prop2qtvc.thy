theory binomial_Top_prop2qtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts infix_sl :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where infix_sl_def:   "infix_sl x y = x ediv y"
 if "\<not>y = (0 :: int)"
  for y :: "int"
  and x :: "int"
consts comb :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where comb_def:   "if k = (0 :: int) \<or> k = n then comb n k = (1 :: int) else comb n k = comb (n - (1 :: int)) k + comb (n - (1 :: int)) (k - (1 :: int))"
 if "(0 :: int) \<le> k"
 and "k \<le> n"
  for k :: "int"
  and n :: "int"
axiomatization where comb'spec:   "(1 :: int) \<le> comb n k"
 if "(0 :: int) \<le> k"
 and "k \<le> n"
  for k :: "int"
  and n :: "int"
theorem prop2'vc:
  fixes k :: "int"
  fixes n :: "int"
  assumes fact0: "(1 :: int) \<le> k"
  assumes fact1: "k \<le> n"
  shows "k * comb n k = comb n (k - (1 :: int)) * (n - k + (1 :: int))"
  sorry
end
