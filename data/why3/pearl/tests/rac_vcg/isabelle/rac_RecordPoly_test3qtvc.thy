theory rac_RecordPoly_test3qtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a t1 = t1'mk (x: "'a")
datatype 'a t2 = t2'mk (f: "int \<Rightarrow> 'a")
datatype 'a t3 = t3'mk (elts: "int \<Rightarrow> 'a") (length: "int")
consts o1 :: "int \<Rightarrow> bool"
consts o2 :: "int \<Rightarrow> bool"
axiomatization where o1_def:   "o1 x = True"
  for x :: "int"
axiomatization where o2_def:   "o2 x = True"
  for x :: "int"
theorem test3'vc:
  shows "(0 :: int) < (3 :: int)"
  and "(3 :: int) < (5 :: int)"
  sorry
end
