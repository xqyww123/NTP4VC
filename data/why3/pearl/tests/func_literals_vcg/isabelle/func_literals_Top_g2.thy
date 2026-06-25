theory func_literals_Top_g2
  imports "NTP4Verif.NTP4Verif"
begin
consts fc :: "int \<Rightarrow> int"
consts fc1 :: "int \<Rightarrow> int"
consts fc2 :: "int \<Rightarrow> int"
axiomatization where fc_def:   "fc x'x = (if x'x = (0 :: int) then 1 :: int else if x'x = (1 :: int) then 42 :: int else (42 :: int))"
  for x'x :: "int"
axiomatization where fc1_def:   "fc1 x'x = (if x'x = (0 :: int) then 1 :: int else if x'x = (1 :: int) then 42 :: int else (42 :: int))"
  for x'x :: "int"
axiomatization where fc2_def:   "fc2 x'x = (if x'x = (1 :: int) then 2 :: int else if x'x = (9 :: int) then 42 :: int else (42 :: int))"
  for x'x :: "int"
theorem g2:
  fixes x :: "int"
  fixes y :: "int"
  assumes fact0: "(1 :: int) < x"
  assumes fact1: "(1 :: int) < y"
  shows "fc1 x = fc2 y"
  sorry
end
