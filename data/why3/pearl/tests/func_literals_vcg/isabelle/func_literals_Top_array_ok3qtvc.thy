theory func_literals_Top_array_ok3qtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts o1 :: "int \<Rightarrow> int \<Rightarrow> int"
consts o2 :: "int \<Rightarrow> int \<Rightarrow> int"
consts fc :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where o1_def:   "o1 default x'x = (if x'x = (0 :: int) then 0 :: int else if x'x = (1 :: int) then 1 :: int else if x'x = (2 :: int) then 2 :: int else if x'x = (3 :: int) then 3 :: int else default)"
  for default :: "int"
  and x'x :: "int"
axiomatization where o2_def:   "o2 default x'x = (if x'x = (0 :: int) then 0 :: int else if x'x = (1 :: int) then 1 :: int else if x'x = (2 :: int) then 2 :: int else if x'x = (3 :: int) then 3 :: int else default)"
  for default :: "int"
  and x'x :: "int"
axiomatization where fc_def:   "fc default x'x = (if x'x = (0 :: int) then 0 :: int else if x'x = (1 :: int) then 1 :: int else if x'x = (2 :: int) then 2 :: int else if x'x = (3 :: int) then 3 :: int else default)"
  for default :: "int"
  and x'x :: "int"
theorem array_ok3'vc:
  fixes default :: "int"
  shows "(0 :: int) \<le> (4 :: int)"
  and "\<forall>(result :: int list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (4 :: int) \<longrightarrow> result ! nat i = o2 default i) \<and> int (length result) = (4 :: int) \<longrightarrow> result = create_list (4 :: int) (fc default)"
  sorry
end
