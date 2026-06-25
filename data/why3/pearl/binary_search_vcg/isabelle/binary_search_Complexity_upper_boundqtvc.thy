theory binary_search_Complexity_upper_boundqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts log2 :: "int \<Rightarrow> int"
axiomatization where log2_def:   "if n \<le> (1 :: int) then log2 n = (0 :: int) else log2 n = (1 :: int) + log2 (n cdiv (2 :: int))"
  for n :: "int"
definition f :: "int \<Rightarrow> int"
  where "f n = (if n = (0 :: int) then 0 :: int else (1 :: int) + log2 n)" for n
theorem upper_bound'vc:
  fixes n :: "int"
  assumes fact0: "(2 :: int) \<le> n"
  shows "f n \<le> (2 :: int) * log2 n"
  sorry
end
