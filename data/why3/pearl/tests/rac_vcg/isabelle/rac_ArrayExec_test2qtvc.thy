theory rac_ArrayExec_test2qtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype 'a array = array'mk (length: "int") (elts: "int \<Rightarrow> 'a")
consts map_update :: "(int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where map_update_def:   "map_update f i x j = (if j = i then x else f j)"
  for f :: "int \<Rightarrow> 'a"
  and i :: "int"
  and x :: "'a"
  and j :: "int"
definition mixfix_lbrb' :: "'a array \<Rightarrow> int \<Rightarrow> 'a"
  where "mixfix_lbrb' a i = elts a i" for a i
consts o1 :: "int \<Rightarrow> int"
consts o2 :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int"
axiomatization where o1_def:   "o1 x = (0 :: int)"
  for x :: "int"
axiomatization where o2_def:   "o2 o3 i = (if i = (0 :: int) then 11 :: int else o3 i)"
  for o3 :: "int \<Rightarrow> int"
  and i :: "int"
theorem test2'vc:
  shows "True"
  sorry
end
