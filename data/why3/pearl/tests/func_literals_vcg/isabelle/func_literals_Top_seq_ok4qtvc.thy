theory func_literals_Top_seq_ok4qtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts o1 :: "int \<Rightarrow> int \<Rightarrow> int"
consts fc :: "int \<Rightarrow> int \<Rightarrow> int"
axiomatization where o1_def:   "o1 default x'x = (if x'x = (0 :: int) then 0 :: int else if x'x = (1 :: int) then 1 :: int else if x'x = (2 :: int) then 2 :: int else if x'x = (3 :: int) then 3 :: int else default)"
  for default :: "int"
  and x'x :: "int"
axiomatization where fc_def:   "fc default x'x = (if x'x = (0 :: int) then 0 :: int else if x'x = (1 :: int) then 1 :: int else if x'x = (2 :: int) then 2 :: int else if x'x = (3 :: int) then 3 :: int else default)"
  for default :: "int"
  and x'x :: "int"
theorem seq_ok4'vc:
  fixes default :: "int"
  shows "let o2 :: int \<Rightarrow> int = o1 default in (0 :: int) \<le> (4 :: int) \<and> (let result :: int list = create_list (4 :: int) o2 in int (length result) = (4 :: int) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (4 :: int) \<longrightarrow> result ! nat i = o2 i) \<longrightarrow> result = create_list (4 :: int) (fc default))"
  sorry
end
