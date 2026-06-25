theory binomial_Top_combqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts infix_sl :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where infix_sl_def:   "infix_sl x y = x ediv y"
 if "\<not>y = (0 :: int)"
  for y :: "int"
  and x :: "int"
theorem comb'vc:
  fixes k :: "int"
  fixes n :: "int"
  fixes o1 :: "bool"
  assumes fact0: "(0 :: int) \<le> k"
  assumes fact1: "k \<le> n"
  assumes fact2: "if k = (0 :: int) then o1 = True else o1 = (if k = n then True else False)"
  shows "\<not>o1 = True \<longrightarrow> (let o2 :: int = k - (1 :: int); o3 :: int = n - (1 :: int) in (((0 :: int) \<le> n \<and> o3 < n) \<and> (0 :: int) \<le> o2 \<and> o2 \<le> o3) \<and> (\<forall>(o4 :: int). (1 :: int) \<le> o4 \<longrightarrow> (let o5 :: int = n - (1 :: int) in ((0 :: int) \<le> n \<and> o5 < n) \<and> (0 :: int) \<le> k \<and> k \<le> o5)))"
  and "\<forall>(result :: int). (if o1 = True then result = (1 :: int) else \<exists>(o2 :: int). (1 :: int) \<le> o2 \<and> (\<exists>(o3 :: int). (1 :: int) \<le> o3 \<and> result = o3 + o2)) \<longrightarrow> (1 :: int) \<le> result"
  sorry
end
