theory binary_search_Complexity_log2_monotoneqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts log2 :: "int \<Rightarrow> int"
axiomatization where log2_def:   "if n \<le> (1 :: int) then log2 n = (0 :: int) else log2 n = (1 :: int) + log2 (n cdiv (2 :: int))"
  for n :: "int"
theorem log2_monotone'vc:
  fixes x :: "int"
  fixes y :: "int"
  assumes fact0: "x \<le> y"
  shows "log2 x \<le> log2 y"
  sorry
end
