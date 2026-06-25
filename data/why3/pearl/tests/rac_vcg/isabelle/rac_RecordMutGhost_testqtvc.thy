theory rac_RecordMutGhost_testqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype  t = t'mk (f: "int \<Rightarrow> int") (n: "int")
consts identity :: "int \<Rightarrow> int"
consts o1 :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int"
axiomatization where identity_def:   "identity y = y"
  for y :: "int"
axiomatization where o1_def:   "o1 o2 z = (if z = (3 :: int) then 42 :: int else o2 z)"
  for o2 :: "int \<Rightarrow> int"
  and z :: "int"
theorem test'vc:
  shows "True"
  sorry
end
