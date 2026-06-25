theory nistonacci_Top_nistonacciqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts nist :: "int \<Rightarrow> int"
axiomatization where nist_def:   "if n < (2 :: int) then nist n = n else nist n = nist (n - (2 :: int)) + (2 :: int) * nist (n - (1 :: int))"
 if "(0 :: int) \<le> n"
  for n :: "int"
theorem nistonacci'vc:
  fixes n :: "int"
  assumes fact0: "(0 :: int) \<le> n"
  shows "let o1 :: int = n - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> ((0 :: int) = nist (0 :: int) \<and> (1 :: int) = nist ((0 :: int) + (1 :: int))) \<and> (\<forall>(y :: int) (x :: int). (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i \<le> o1) \<and> x = nist i \<and> y = nist (i + (1 :: int)) \<longrightarrow> y = nist (i + (1 :: int)) \<and> x + (2 :: int) * y = nist (i + (1 :: int) + (1 :: int))) \<and> (x = nist (o1 + (1 :: int)) \<and> y = nist (o1 + (1 :: int) + (1 :: int)) \<longrightarrow> x = nist n))) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> (0 :: int) = nist n)"
  sorry
end
