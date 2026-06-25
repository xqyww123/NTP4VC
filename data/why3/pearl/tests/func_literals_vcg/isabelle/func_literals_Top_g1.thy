theory func_literals_Top_g1
  imports "NTP4Verif.NTP4Verif"
begin
consts fc :: "int \<Rightarrow> int"
consts fc1 :: "int \<Rightarrow> int"
axiomatization where fc_def:   "fc x'x = (if x'x = (0 :: int) then 1 :: int else (1 :: int))"
  for x'x :: "int"
axiomatization where fc1_def:   "fc1 x'x = (if x'x = (1 :: int) then 2 :: int else (2 :: int))"
  for x'x :: "int"
theorem g1:
  shows "let a :: int \<Rightarrow> int = fc; b :: int \<Rightarrow> int = fc1 in (1 :: int) = a (1 :: int) \<and> \<not>a (1 :: int) = b (1 :: int) \<and> b (1 :: int) = (2 :: int)"
  sorry
end
