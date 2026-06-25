theory func_literals_Top_g3
  imports "NTP4Verif.NTP4Verif"
begin
consts fc :: "int \<Rightarrow> int"
consts fc1 :: "int \<Rightarrow> int"
axiomatization where fc_def:   "fc x'x = (if x'x = (0 :: int) then 1 :: int else if x'x = (1 :: int) then 2 :: int else (2 :: int))"
  for x'x :: "int"
axiomatization where fc1_def:   "fc1 x'x = (if x'x = (0 :: int) then 1 :: int else if x'x = (1 :: int) then -(2 :: int) else -(2 :: int))"
  for x'x :: "int"
theorem g3:
  shows "let a :: int \<Rightarrow> int = fc; b :: int \<Rightarrow> int = fc1 in a (0 :: int) = b (0 :: int) \<and> a (1 :: int) = -b (1 :: int) \<and> a (2 :: int) = -b (3 :: int) \<and> a (3 :: int) = -b (3 :: int) \<and> \<not>a (3 :: int) = b (3 :: int)"
  sorry
end
