theory nistonacci_Top_test
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
consts nist :: "int \<Rightarrow> int"
axiomatization where nist_def:   "if n < (2 :: int) then nist n = n else nist n = nist (n - (2 :: int)) + (2 :: int) * nist (n - (1 :: int))"
 if "(0 :: int) \<le> n"
  for n :: "int"
theorem test:
  shows "(17 :: int) \<le> nist (42 :: int)"
  sorry
end
