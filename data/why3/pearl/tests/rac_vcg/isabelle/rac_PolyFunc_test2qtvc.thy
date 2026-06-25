theory rac_PolyFunc_test2qtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a t = t'mk (f: "int \<Rightarrow> 'a")
consts map_update :: "(int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where map_update_def:   "map_update f1 i x j = (if j = i then x else f1 j)"
  for f1 :: "int \<Rightarrow> 'a"
  and i :: "int"
  and x :: "'a"
  and j :: "int"
consts o1 :: "int \<Rightarrow> int"
axiomatization where o1_def:   "o1 x = (0 :: int)"
  for x :: "int"
theorem test2'vc:
  shows "True"
  sorry
end
