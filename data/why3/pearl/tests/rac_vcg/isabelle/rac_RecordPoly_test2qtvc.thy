theory rac_RecordPoly_test2qtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a t1 = t1'mk (x: "'a")
datatype 'a t2 = t2'mk (f: "int \<Rightarrow> 'a")
consts o1 :: "int \<Rightarrow> bool"
axiomatization where o1_def:   "o1 x = True"
  for x :: "int"
theorem test2'vc:
  shows "True"
  sorry
end
